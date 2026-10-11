#include "Checker.h"
#include "ScopedWitness.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include <algorithm>
#include <numeric>
using namespace llvm;
namespace zkc::language::detail {
Checker::Checker(std::vector<SyntaxDeclaration> syntax, CheckedStorage &output,
                 Work &work)
    : output(output), work(work),
      types(output.declarations, output.assets, work,
            [this](DeclarationId id) { return signature(id); }),
      syntax(std::move(syntax)) {}
Error Checker::run() {
  if (auto error = checkCapabilityInstallation())
    return error;
  if (!collect() || !imports() || !prepareNotationSyntax())
    return types.takeError();
  std::vector<std::vector<BodyParseScope>> bodyScopes(output.sources->size());
  for (auto id : moduleIds) {
    auto *module = sources[id.index];
    bodyScopes[module->span.source.index].push_back(
        {module, notationEnvironments[id.index]});
  }
  for (unsigned i = 0; i < bodyScopes.size(); ++i)
    if (auto error = parseBodies((*output.sources)[i], SourceId{i},
                                 output.tokens[i], bodyScopes[i], work))
      return error;
  for (auto &decl : output.declarations)
    if (!decl.abstract && !sources[decl.id.index]->explicitRequirements &&
        (decl.kind == Declaration::Kind::Math ||
         decl.kind == Declaration::Kind::Local ||
         decl.kind == Declaration::Kind::Protocol))
      inferredContracts.insert(&decl);
  types.inferCapability = [this](const Declaration *scope,
                                 const CapabilityBound &bound) {
    if (!inferredContracts.count(scope))
      return false;
    auto requirement = bound;
    requirement.inferred = true;
    output.declarations[scope->id.index].capabilityBounds.push_back(
        std::move(requirement));
    return true;
  };
  types.inferNatural = [this](const Declaration &scope,
                              const NaturalBound &bound) {
    if (!inferredContracts.count(&scope))
      return false;
    auto requirement = bound;
    requirement.inferred = true;
    output.declarations[scope.id.index].bounds.push_back(
        std::move(requirement));
    return true;
  };
  signatureState.resize(output.declarations.size());
  for (unsigned i = 0; i < output.declarations.size(); ++i)
    if (!sources[i]->constructionHandler && !signature(DeclarationId{i}))
      return types.takeError();
  if (!prepareOperators())
    return types.takeError();
  if (!relationIdentities())
    return types.takeError();
  bodyState.resize(output.declarations.size());
  bodyHeights.resize(bodyState.size());
  for (auto &decl : output.declarations)
    if (decl.kind == Declaration::Kind::Module && decl.implementation &&
        !conformance(decl.id))
      return types.takeError();
  if (!representations())
    return types.takeError();
  for (auto &decl : output.declarations)
    if (decl.kind == Declaration::Kind::Record ||
        decl.kind == Declaration::Kind::Variant) {
      Type nominal(decl.kind == Declaration::Kind::Record ? Type::Kind::Record
                                                          : Type::Kind::Variant,
                   decl.qualifiedName);
      for (const auto &parameter : decl.parameters)
        nominal.arguments.push_back(parameterType(parameter));
      if (!types.permissions(nominal, decl.span, &decl))
        return types.takeError();
    }
  for (const auto &decl : output.declarations)
    if (decl.kind == Declaration::Kind::Math)
      for (auto *ports : {&decl.inputs, &decl.outputs})
        for (const auto &port : *ports) {
          auto caps = types.permissions(port.type, port.span, &decl);
          if (!caps)
            return types.takeError();
          if (!caps->copy || !caps->drop) {
            types.fail("source.mode",
                       "mathematical signatures require Copy and Drop",
                       port.span);
            return types.takeError();
          }
        }
  for (unsigned i = 0; i < sources.size(); ++i) {
    auto &decl = output.declarations[i];
    if ((decl.kind == Declaration::Kind::Math ||
         decl.kind == Declaration::Kind::Local ||
         decl.kind == Declaration::Kind::DomainFunction ||
         decl.kind == Declaration::Kind::Protocol ||
         (decl.kind == Declaration::Kind::Relation &&
          decl.relation->kind == RelationDefinition::Kind::Formula)) &&
        !decl.abstract && !sources[i]->constructionHandler && !body(decl.id, 1))
      return types.takeError();
  }
  if (!constructions() || !entries())
    return types.takeError();
  inferredContracts.clear();
  types.inferCapability = {};
  types.inferNatural = {};
  if (!retainNotations() || !retainScopedSources())
    return types.takeError();
  return checkScopedSources(output, work);
}
std::shared_ptr<const SyntaxDeclaration>
Checker::retainSyntax(DeclarationId owner) {
  // Run after all source consumers (including notation retention) have
  // finished. Different witnesses for one declaration share the same immutable
  // syntax.
  if (!types.charge(1, output.declarations[owner.index].span))
    return {};
  auto &retained = retainedSyntax[owner.index];
  if (!retained)
    retained =
        std::make_shared<SyntaxDeclaration>(std::move(*sources[owner.index]));
  return retained;
}
bool Checker::bindingName(const Declaration &decl, StringRef name, Span span) {
  if (llvm::any_of(decl.parameters, [&](auto &p) { return p.name == name; }))
    return types.fail("source.shadow", "binding shadows a static parameter",
                      span);
  for (auto scope = std::optional(decl.module); scope;
       scope = output.declarations[scope->index].parent) {
    if (visible[scope->index].count(name.str()))
      return types.fail("source.shadow",
                        "binding shadows a visible declaration", span);
  }
  return true;
}
bool Checker::collect() {
  std::map<std::string, SyntaxDeclaration *> files;
  std::set<std::string> linked;
  for (auto &root : syntax)
    files.emplace(root.name, &root);
  std::function<bool(SyntaxDeclaration &, DeclarationId,
                     std::optional<DeclarationId>, std::string, unsigned)>
      add;
  add = [&](SyntaxDeclaration &written, DeclarationId module,
            std::optional<DeclarationId> parent, std::string path,
            unsigned depth) {
    if (depth > work.limits.parseDepth || !types.charge(1, written.span))
      return types.diagnostic
                 ? false
                 : types.fail("source.limit", "module nesting limit",
                              written.span);
    SyntaxDeclaration *definition = &written;
    if (written.externalModule) {
      auto found = files.find(path);
      if (found == files.end())
        return types.fail("source.module",
                          "external module was not captured: " + path,
                          written.span);
      if ((*output.sources)[found->second->span.source.index].origin ==
          SourceOrigin::Installation)
        return types.fail("source.module",
                          "installation modules cannot be linked as children",
                          written.span);
      if (!linked.insert(path).second)
        return types.fail("source.duplicate",
                          "external module was linked twice", written.span);
      definition = found->second;
      definition->isPublic = written.isPublic;
    } else if (parent && files.count(path))
      return types.fail("source.duplicate",
                        "captured module path collides with a declaration",
                        written.span);
    auto &source = *definition;
    Declaration decl;
    decl.id = {uint32_t(output.declarations.size())};
    decl.module = source.kind == Declaration::Kind::Module ? decl.id : module;
    decl.kind = source.kind;
    decl.name = StringRef(path).rsplit("::").second.str();
    if (decl.name.empty())
      decl.name = path;
    decl.parent = parent;
    decl.span = source.span;
    decl.qualifiedName = std::move(path);
    decl.isPublic = source.isPublic;
    decl.abstract = source.abstract;
    decl.completes = source.completes;
    decl.permissions = source.permissions;
    if (source.effects)
      decl.effectAllowance = EffectSummary{*source.effects};
    decl.inputOrder = source.inputOrder;
    decl.associatedSort = source.associatedSort;
    decl.anonymous = source.anonymous;
    decl.specificationBlock = source.specificationBlock;
    decl.proofFormat = source.proofFormat;
    if (source.relation) {
      const auto &definition = *source.relation;
      decl.relation = RelationDefinition{
          definition.kind,     {}, definition.externalKind, definition.key,
          definition.revision, {}};
      for (const auto &port : source.inputs)
        decl.relation->purposes.push_back(*port.purpose);
    }
    if (decl.anonymous)
      decl.qualifiedName = output.declarations[parent->index].qualifiedName +
                           "::<" + source.name + ">";
    if (!decl.anonymous &&
        !qualified.emplace(decl.qualifiedName, decl.id).second)
      return types.fail("source.duplicate",
                        "duplicate declaration: " + decl.name, decl.span);
    auto symbol =
        decl.anonymous
            ? Expected<std::string>("zki_" + digest(decl.qualifiedName))
            : encodeSymbol(decl.qualifiedName, work.limits);
    if (!symbol)
      return types.accept(symbol.takeError(), decl.span);
    decl.symbol = std::move(*symbol);
    types.indexDeclaration(decl);
    if (source.kind == Declaration::Kind::Domain && source.assetDomain) {
      // The declaration denotes the captured asset's canonical identity, so
      // every domain naming the same admitted contents is the same term.
      if (!types.charge(output.assets.size() + source.domain.size() + 1,
                        source.span))
        return false;
      auto found = llvm::find_if(output.assets, [&](const Asset &asset) {
        return asset.name() == source.domain;
      });
      if (found == output.assets.end())
        return types.fail("source.asset-reference",
                          "captured asset is absent: " + source.domain,
                          source.span);
      StringRef sort = source.target == "ring" ? "Ring" : "Bundle";
      if (sort == "Ring" ? !found->ring() : !found->bundle())
        return types.fail("source.asset-reference",
                          "captured asset " + source.domain + " is not a " +
                              source.target,
                          source.span);
      decl.domain = assetType(sort, found->identity());
    } else if (source.kind == Declaration::Kind::Domain) {
      auto sorts = protocol::domainSorts();
      auto sort = llvm::find_if(sorts, [&](const std::string &sort) {
        return StringRef(sort).lower() == source.target;
      });
      if (sort == sorts.end())
        return types.fail("source.domain",
                          "unknown domain sort: " + source.target, source.span);
      if (protocol::installedDomains().identitySort(source.domain) != *sort)
        return types.fail("source.domain",
                          "expected installed " + source.target +
                              " identity: " + source.domain,
                          source.span);
      decl.domain = domainType(*sort, source.domain);
    }
    auto id = decl.id;
    sources.push_back(&source);
    visible.emplace_back();
    if (decl.kind == Declaration::Kind::Module) {
      if (!modules.emplace(decl.qualifiedName, id).second)
        return types.fail("source.duplicate", "duplicate module body",
                          decl.span);
      moduleIds.push_back(id);
      module = id;
    }
    if (parent && !decl.anonymous &&
        output.declarations[parent->index].kind == Declaration::Kind::Module)
      visible[parent->index].emplace(
          decl.name, ModuleBinding{id, decl.span, decl.isPublic});
    output.declarations.push_back(std::move(decl));
    if (parent)
      output.declarations[parent->index].members.push_back(id);
    for (auto &member : source.members)
      if (!add(member, module, id,
               output.declarations[id.index].qualifiedName + "::" + member.name,
               depth + 1))
        return false;
    return true;
  };
  // A captured descendant is attached only through an authored child link.
  for (auto &root : syntax) {
    bool descendant = false;
    auto prefix = StringRef(root.name);
    while (prefix.contains("::")) {
      prefix = prefix.rsplit("::").first;
      if ((*output.sources)[root.span.source.index].origin !=
              SourceOrigin::Installation &&
          files.count(prefix.str())) {
        descendant = true;
        break;
      }
    }
    if (!descendant && !add(root, {}, {}, root.name, 1))
      return false;
  }
  for (auto &root : syntax) {
    auto found = modules.find(root.name);
    if (found == modules.end())
      return types.fail("source.module",
                        "captured child needs an external module declaration",
                        root.span);
  }
  return true;
}
std::optional<DeclarationId> Checker::member(const Declaration &context,
                                             DeclarationId owner,
                                             StringRef name, Span span) {
  const auto &decl = output.declarations[owner.index];
  if (!types.charge(1, span))
    return {};
  auto check = [&](DeclarationId target, bool isPublic,
                   Span definition) -> std::optional<DeclarationId> {
    if (checkingVisibility && !isPublic &&
        !types.withinModule(context.module, decl.module)) {
      types.fail("source.private",
                 "cannot reference private declaration: " + name, span,
                 {definition});
      return {};
    }
    return target;
  };
  if (decl.kind == Declaration::Kind::Module) {
    if (loadBinding && !loadBinding(owner, name))
      return {};
    auto found = visible[owner.index].find(name.str());
    if (found != visible[owner.index].end())
      return check(found->second.target, found->second.isPublic,
                   found->second.span);
  } else {
    if (!types.charge(decl.members.size(), span))
      return {};
    for (auto id : decl.members) {
      const auto &child = output.declarations[id.index];
      if (!child.anonymous && child.name == name)
        return check(id, child.isPublic, child.span);
    }
  }
  return {};
}
std::optional<DeclarationId>
Checker::resolve(const Declaration &context, StringRef name, Span span,
                 bool required, std::vector<ModuleLookup> *route) {
  if (!types.charge(1, span))
    return {};
  const bool absolute = name.consume_front("::");
  auto [head, tail] = name.split("::");
  std::optional<DeclarationId> root;
  if (!absolute) {
    auto scope = context.kind == Declaration::Kind::Module
                     ? std::optional(context.id)
                     : context.parent;
    for (; scope; scope = output.declarations[scope->index].parent) {
      root = member(context, *scope, head, span);
      if (types.diagnostic)
        return {};
      if (root) {
        if (route)
          route->push_back({*scope, head.str()});
        break;
      }
    }
  }
  if (!root) {
    // Only source roots enter global lookup. Descendants are reached through
    // actual bindings, so absolute paths and aliases obey the same privacy.
    StringRef prefix = name;
    while (!prefix.empty()) {
      auto found = modules.find(prefix.str());
      if (found != modules.end() &&
          !output.declarations[found->second.index].parent) {
        root = found->second;
        tail = name.size() == prefix.size()
                   ? StringRef{}
                   : name.drop_front(prefix.size() + 2);
        break;
      }
      prefix = prefix.contains("::") ? prefix.rsplit("::").first : StringRef{};
    }
  }
  while (root && !tail.empty()) {
    auto next = tail.split("::");
    auto owner = *root;
    root = member(context, owner, next.first, span);
    if (root && route)
      route->push_back({owner, next.first.str()});
    if (types.diagnostic)
      return {};
    tail = next.second;
  }
  if (!root && required)
    types.fail("source.name", "unknown declaration: " + name, span);
  return root;
}
std::optional<std::vector<unsigned>> Checker::roles(const Declaration &decl,
                                                    ArrayRef<std::string> names,
                                                    Span span) {
  if (!types.charge(names.size() * (decl.roles.size() + 1), span))
    return {};
  std::vector<unsigned> result;
  for (auto &name : names) {
    auto found = llvm::find(decl.roles, name);
    if (found == decl.roles.end()) {
      types.fail("source.roles", "unknown participant: " + name, span);
      return {};
    }
    result.push_back(found - decl.roles.begin());
  }
  llvm::sort(result);
  if (result.empty() ||
      std::adjacent_find(result.begin(), result.end()) != result.end()) {
    types.fail("source.roles", "role set must be nonempty and distinct", span);
    return {};
  }
  return result;
}
Error check(std::vector<SyntaxDeclaration> syntax, CheckedStorage &output,
            Work &work) {
  return Checker(std::move(syntax), output, work).run();
}
} // namespace zkc::language::detail
