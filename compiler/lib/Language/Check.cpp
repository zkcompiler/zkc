#include "Checker.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include <algorithm>
#include <numeric>
using namespace llvm;
namespace zkc::language::detail {
Checker::Checker(std::vector<SyntaxModule> syntax, CheckedStorage &output,
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
  for (auto &module : syntax)
    if (auto error = parseBodies((*output.sources)[module.id.index], module,
                                 output.tokens[module.id.index],
                                 notationEnvironments[module.id.index], work))
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
    if (!signature(DeclarationId{i}))
      return types.takeError();
  if (!prepareOperators())
    return types.takeError();
  if (!relationIdentities())
    return types.takeError();
  bodyState.resize(output.declarations.size());
  bodyHeights.resize(bodyState.size());
  for (auto &decl : output.declarations)
    if (decl.kind == Declaration::Kind::Component && !conformance(decl.id))
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
         decl.kind == Declaration::Kind::Protocol ||
         (decl.kind == Declaration::Kind::Relation &&
          decl.relation->kind == RelationDefinition::Kind::Formula)) &&
        !decl.abstract && !body(decl.id, 1))
      return types.takeError();
  }
  if (!entries())
    return types.takeError();
  inferredContracts.clear();
  types.inferCapability = {};
  types.inferNatural = {};
  if (!finalizeReductions() || !retainNotations() || !retainReductionSources())
    return types.takeError();
  return checkReductions(output, work);
}
bool Checker::bindingName(const Declaration &decl, StringRef name, Span span) {
  if (visible[decl.module.index].count(name.str()) ||
      aliases[decl.module.index].count(name.str()) ||
      llvm::any_of(decl.parameters, [&](auto &p) { return p.name == name; }))
    return types.fail("source.shadow",
                      "binding shadows a visible declaration, module alias or "
                      "static parameter",
                      span);
  return true;
}
bool Checker::collect() {
  visible.resize(syntax.size());
  std::function<bool(SyntaxDeclaration &, ModuleId,
                     std::optional<DeclarationId>)>
      add;
  add = [&](SyntaxDeclaration &source, ModuleId module,
            std::optional<DeclarationId> parent) {
    Declaration decl;
    decl.id = {uint32_t(output.declarations.size())};
    decl.module = module;
    decl.kind = source.kind;
    decl.name = source.name;
    decl.parent = parent;
    decl.span = source.span;
    decl.qualifiedName =
        (parent ? output.declarations[parent->index].qualifiedName
                : (*output.sources)[module.index].module) +
        "::" + source.name;
    decl.isPublic = source.isPublic;
    decl.abstract = source.abstract;
    decl.completes = source.completes;
    decl.permissions = source.permissions;
    decl.effectAllowance = source.effects;
    decl.inputOrder = source.inputOrder;
    decl.associatedSort = source.associatedSort;
    decl.anonymous = source.anonymous;
    decl.specificationBlock = source.specificationBlock;
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
    if (!parent && !visible[module.index].emplace(decl.name, decl.id).second)
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
    output.declarations.push_back(std::move(decl));
    if (parent)
      output.declarations[parent->index].members.push_back(id);
    for (auto &member : source.members)
      if (!add(member, module, id))
        return false;
    return true;
  };
  for (auto &module : syntax) {
    modules.emplace((*output.sources)[module.id.index].module, module.id);
    for (auto &decl : module.declarations)
      if (!add(decl, module.id, {}))
        return false;
  }
  return true;
}
std::optional<DeclarationId> Checker::resolve(const Declaration &context,
                                              StringRef name, Span span,
                                              bool required) {
  if (!types.charge(1, span))
    return {};
  const bool absolute = name.consume_front("::");
  auto [head, tail] = name.split("::");
  auto member = [&](DeclarationId owner,
                    StringRef part) -> std::optional<DeclarationId> {
    const auto &members = output.declarations[owner.index].members;
    if (!types.charge(members.size(), span))
      return {};
    for (auto id : members)
      if (!output.declarations[id.index].anonymous &&
          output.declarations[id.index].name == part)
        return id;
    return {};
  };
  std::optional<DeclarationId> root;
  std::optional<ModuleId> moduleRoot;
  if (!absolute) {
    for (auto parent = context.parent; parent;
         parent = output.declarations[parent->index].parent) {
      root = member(*parent, head);
      if (types.diagnostic)
        return {};
      if (root)
        break;
    }
    if (!root) {
      auto found = visible[context.module.index].find(head.str());
      if (found != visible[context.module.index].end())
        root = found->second;
      else if (auto alias = aliases[context.module.index].find(head.str());
               alias != aliases[context.module.index].end())
        moduleRoot = alias->second;
    }
  }
  // Descend actual declaration members. A same-named captured module is not
  // part of a lexical declaration's scope, including when a member is absent.
  std::optional<DeclarationId> resolved = root;
  if (root) {
    while (resolved && !tail.empty()) {
      if (!types.charge(1, span))
        return {};
      auto next = tail.split("::");
      resolved = member(*resolved, next.first);
      if (types.diagnostic)
        return {};
      tail = next.second;
    }
  } else if (moduleRoot) {
    resolved = moduleMember(*moduleRoot, tail, span);
  } else if (auto found = qualified.find(name.str());
             found != qualified.end()) {
    resolved = found->second;
  } else {
    auto prefix = name.contains("::") ? name.rsplit("::").first : StringRef{};
    while (!prefix.empty()) {
      auto module = modules.find(prefix.str());
      if (module != modules.end()) {
        resolved = moduleMember(module->second,
                                name.drop_front(prefix.size() + 2), span);
        break;
      }
      prefix = prefix.contains("::") ? prefix.rsplit("::").first : StringRef{};
    }
  }
  if (!resolved) {
    if (required)
      types.fail("source.name", "unknown declaration: " + name, span);
    return {};
  }
  auto id = *resolved;
  for (auto current = std::optional<DeclarationId>{id}; current;
       current = output.declarations[current->index].parent) {
    const auto &ancestor = output.declarations[current->index];
    if (ancestor.module.index != context.module.index && !ancestor.isPublic) {
      types.fail("source.private",
                 "cannot reference private declaration: " + name, span,
                 {ancestor.span});
      return {};
    }
  }
  return id;
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
Error check(std::vector<SyntaxModule> syntax, CheckedStorage &output,
            Work &work) {
  return Checker(std::move(syntax), output, work).run();
}
} // namespace zkc::language::detail
