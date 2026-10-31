#include "Checker.h"
#include "ScopedWitness.h"
#include "WrittenSource.h"
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
Checker::Checker(CheckedStorage &output, Work &work,
                 const NameEnvironment &names)
    : Checker({}, output, work) {
  modules = names.modules;
  visible = names.visible;
  signatureState.assign(output.declarations.size(), 2);
  externalSelection = true;
  for (const auto &decl : output.declarations)
    if (decl.kind == Declaration::Kind::Module &&
        (*output.sources)[decl.span.source.index].origin ==
            SourceOrigin::Captured) {
      if (!decl.parent)
        externalNames[decl.qualifiedName].insert(decl.id.index);
      for (const auto &[name, binding] : visible[decl.id.index])
        externalNames[name].insert(binding.target.index);
    }
}
Error Checker::run() {
  if (auto error = checkCapabilityInstallation())
    return error;
  auto written = retainWrittenHeaders(syntax, work);
  if (!written)
    return written.takeError();
  if (auto error = expandLayoutSections(syntax, work))
    return error;
  if (!collect() || !imports() || !classifyServices() ||
      !prepareNotationSyntax())
    return types.takeError();
  namesReady = true;
  std::vector<std::vector<BodyParseScope>> bodyScopes(output.sources->size());
  for (auto id : moduleIds) {
    auto *module = sources[id.index];
    bodyScopes[module->span.source.index].push_back(
        {module, notationEnvironments[id.index]});
  }
  for (const auto &decl : output.declarations)
    if (decl.kind == Declaration::Kind::Interface &&
        sources[decl.id.index]->layoutSyntax)
      bodyScopes[decl.span.source.index].push_back(
          {sources[decl.id.index], notationEnvironments[decl.module.index]});
  for (unsigned i = 0; i < bodyScopes.size(); ++i) {
    auto error = output.layoutHeaders[i]
                     ? parseLayoutBodies(SourceId{i}, bodyScopes[i], output,
                                         work, recoveryDiagnostics)
                     : parseBodies((*output.sources)[i], SourceId{i},
                                   output.tokens[i], bodyScopes[i], work);
    if (error)
      return error;
  }
  if (!prepareOraclePredicates() || !layoutSpecifications())
    return types.takeError();
  if (!recoveryDiagnostics || recoveryDiagnostics->empty()) {
    if (auto error = retainWrittenBodies(**written, sources, work))
      return error;
    output.writtenSources = std::move(*written);
  }
  for (auto &decl : output.declarations)
    if (!decl.abstract && !sources[decl.id.index]->explicitRequirements &&
        (decl.kind == Declaration::Kind::Oracle ||
         decl.kind == Declaration::Kind::Math ||
         decl.kind == Declaration::Kind::Local ||
         decl.kind == Declaration::Kind::EntryFunction ||
         decl.kind == Declaration::Kind::DomainFunction ||
         decl.kind == Declaration::Kind::Protocol ||
         decl.kind == Declaration::Kind::Construction))
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
  types.collectUsage = [this](const Declaration &scope, const Type &type,
                              Usage usage, Span span, StringRef code,
                              StringRef message) {
    return collectUsage(scope, type, usage, span, code, message);
  };
  // The vector is the checked contract; this index only accelerates collection.
  // Repeated sites need one condition, with one representative origin chain.
  std::map<unsigned, std::map<std::pair<Boundary, std::string>, unsigned>>
      admissionIndices;
  types.recordAdmission = [this,
                           &admissionIndices](const Declaration &scope,
                                              AdmissionObligation obligation) {
    if (!types.chargeType(obligation.type, obligation.span) ||
        !types.charge(obligation.calls.size() + 1, obligation.span))
      return false;
    auto &admissions = output.declarations[scope.id.index].admissions;
    auto key =
        std::make_pair(obligation.boundary, typeIdentity(obligation.type));
    auto [at, inserted] = admissionIndices[scope.id.index].emplace(
        std::move(key), admissions.size());
    if (inserted)
      admissions.push_back(std::move(obligation));
    else if (obligation.calls.size() < admissions[at->second].calls.size())
      admissions[at->second] = std::move(obligation);
    return true;
  };
  signatureState.resize(output.declarations.size());
  bodyState.resize(output.declarations.size());
  bodyHeights.resize(output.declarations.size());
  entryStates.resize(output.declarations.size());
  bool failedSignatures = false;
  for (unsigned i = 0; i < output.declarations.size(); ++i)
    if (!sources[i]->constructionHandler && !signature(DeclarationId{i})) {
      failedSignatures = true;
      auto error = types.takeError();
      if (!recoveryDiagnostics)
        return error;
      if (!recover(std::move(error)))
        return Error::success();
    }
  // Invalid signatures can affect overload and representation formation.
  // Preserve the independent signature facts, without running those phases.
  if (failedSignatures)
    return Error::success();
  if (!prepareOperators())
    return types.takeError();
  if (!relationIdentities())
    return types.takeError();
  if (!pendingClaimRelations())
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
      Type nominal(
          decl.kind == Declaration::Kind::Record
              ? (decl.logical ? Type::Kind::LogicalRecord : Type::Kind::Record)
              : Type::Kind::Variant,
          decl.qualifiedName);
      for (const auto &parameter : decl.parameters)
        nominal.arguments.push_back(parameterType(parameter));
      if (!types.permissions(nominal, decl.span, &decl))
        return types.takeError();
    } else if (decl.kind == Declaration::Kind::Associated && !decl.abstract &&
               !isStaticOnly(decl.domain)) {
      const auto &owner = output.declarations[decl.parent->index];
      Type module(Type::Kind::Module, owner.qualifiedName);
      for (const auto &parameter : owner.parameters)
        module.arguments.push_back(parameterType(parameter));
      Type associated(Type::Kind::Associated, decl.qualifiedName);
      associated.arguments.push_back(std::move(module));
      if (!types.permissions(associated, decl.span, &decl))
        return types.takeError();
    }
  for (const auto &decl : output.declarations)
    if (decl.kind == Declaration::Kind::Math && decl.abstract)
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
    if ((decl.kind == Declaration::Kind::Oracle ||
         decl.kind == Declaration::Kind::Math ||
         decl.kind == Declaration::Kind::Local ||
         decl.kind == Declaration::Kind::EntryFunction ||
         decl.kind == Declaration::Kind::DomainFunction ||
         decl.kind == Declaration::Kind::Protocol ||
         (decl.kind == Declaration::Kind::Relation &&
          decl.relation->kind == RelationDefinition::Kind::Formula)) &&
        !decl.abstract && !decl.generated && !sources[i]->constructionHandler &&
        !sources[i]->invalidBody && !body(decl.id, 1)) {
      auto error = types.takeError();
      if (!recoveryDiagnostics)
        return error;
      if (!recover(std::move(error)))
        return Error::success();
    }
  }
  if (recoveryDiagnostics && !recoveryDiagnostics->empty())
    return Error::success();
  if (!constructions() || !entries() || !sourceClaims())
    return types.takeError();
  inferredContracts.clear();
  types.inferCapability = {};
  types.inferNatural = {};
  types.collectUsage = {};
  types.recordAdmission = {};
  if (!retainAPI() || !retainNotations() || !retainScopedSources())
    return types.takeError();
  output.names = std::make_shared<NameEnvironment>(
      NameEnvironment{std::move(modules), std::move(visible)});
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
  auto scope = decl.kind == Declaration::Kind::Module ? std::optional(decl.id)
                                                      : decl.parent;
  for (; scope; scope = output.declarations[scope->index].parent) {
    if (member(decl, *scope, name, span))
      return types.fail("source.shadow",
                        "binding shadows a visible declaration", span);
    if (types.diagnostic)
      return false;
  }
  return true;
}
bool Checker::collect() {
  std::function<bool(SyntaxDeclaration &)> generated =
      [&](SyntaxDeclaration &source) {
        for (auto &child : source.members)
          if (!generated(child))
            return false;
        using K = Declaration::Kind;
        uint64_t extra =
            source.kind == K::Oracle     ? 1
            : source.kind == K::Protocol ? 3 + 2 * uint64_t(source.roles.size())
            : source.kind == K::Entry && source.entryKind == EntryKind::Proof
                ? 9
                : 0;
        if (extra > work.limits.declarations - work.declarations)
          return types.fail("source.limit", "generated declaration count",
                            source.span);
        if (!types.charge(extra, source.span))
          return false;
        work.declarations += extra;
        auto add = [&](StringRef name,
                       Declaration::Kind kind) -> SyntaxDeclaration & {
          SyntaxDeclaration child;
          child.name = name.str();
          child.kind = kind;
          child.span = source.span;
          child.isPublic = true;
          child.generated = name.str();
          if (kind == Declaration::Kind::Local ||
              kind == Declaration::Kind::EntryFunction)
            child.effects = Effects{true, false};
          source.members.push_back(std::move(child));
          return source.members.back();
        };
        if (source.kind == K::Oracle) {
          SyntaxDeclaration predicate;
          predicate.name = "__oracle_admissibility";
          predicate.kind = K::Relation;
          predicate.span = source.span;
          predicate.oraclePredicate = true;
          predicate.relation.emplace();
          source.members.push_back(std::move(predicate));
        } else if (source.kind == K::Protocol) {
          for (auto member : {"Inputs", "RunResult"}) {
            auto &product = add(member, K::Record);
            for (const auto &role : source.roles) {
              SyntaxDeclaration child;
              child.kind = K::Record;
              child.name = role;
              child.span = source.span;
              child.isPublic = true;
              child.generated = std::string(member) + ":" + role;
              product.members.push_back(std::move(child));
            }
          }
          add("run", K::EntryFunction);
        } else if (source.kind == K::Entry &&
                   source.entryKind == EntryKind::Proof) {
          for (auto member : {"Public", "Witness", "Proof", "ProverOutputs",
                              "VerifierOutputs", "ProveResult"})
            add(member, K::Record);
          add("VerifyResult", K::Variant);
          add("prove", K::Local);
          add("verify", K::Local);
        }
        return types.charge(source.members.size() + 1, source.span);
      };
  for (auto &root : syntax)
    if (!generated(root))
      return false;
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
    if (source.generated) {
      auto target = *parent;
      if (output.declarations[target.index].generated)
        target = output.declarations[target.index].generated->target;
      decl.generated = Declaration::Generated{target, *source.generated};
      std::string identity;
      frame(identity, output.capture.identity());
      frame(identity, output.installation);
      frame(identity, output.declarations[target.index].qualifiedName);
      frame(identity, *source.generated);
      decl.generated->identity = digest(identity);
    }
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
    decl.resource = source.resource;
    decl.logical = source.logical;
    decl.sealed = source.sealed || source.resource.has_value();
    if (source.effects)
      decl.effectAllowance = EffectSummary{*source.effects};
    decl.inputOrder = source.inputOrder;
    decl.associatedSort = source.associatedSort;
    decl.anonymous = source.anonymous;
    decl.specificationBlock = source.specificationBlock;
    for (const auto &block : source.sourceClaims)
      decl.sourceClaims.push_back(block.value);
    decl.sourceVerifications = source.sourceVerifications;
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
    if (parent && !decl.anonymous)
      visible[parent->index].emplace(
          decl.name, ScopeBinding{id, decl.span, decl.isPublic, {}});
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
  if (decl.kind == Declaration::Kind::Module && loadBinding &&
      !loadBinding(owner, name))
    return {};
  auto found = visible[owner.index].find(name.str());
  if (found != visible[owner.index].end())
    return check(found->second.target, found->second.isPublic,
                 found->second.span);
  return {};
}
std::optional<DeclarationId>
Checker::resolve(const Declaration &context, StringRef name, Span span,
                 bool required, std::vector<ModuleLookup> *route,
                 std::optional<DeclarationId> *provider) {
  if (!types.charge(1, span))
    return {};
  const auto written = name;
  std::optional<DeclarationId> selectedProvider;
  const bool absolute = name.consume_front("::");
  auto [head, tail] = name.split("::");
  std::optional<DeclarationId> root;
  if (!absolute && !externalSelection) {
    auto scope = (context.kind == Declaration::Kind::Module ||
                  context.kind == Declaration::Kind::Interface)
                     ? std::optional(context.id)
                     : context.parent;
    for (; scope; scope = output.declarations[scope->index].parent) {
      root = member(context, *scope, head, span);
      if (types.diagnostic)
        return {};
      if (root) {
        const auto &binding = visible[scope->index].at(head.str());
        selectedProvider =
            binding.provider.value_or(output.declarations[root->index].module);
        if (route)
          route->push_back({*scope, head.str()});
        break;
      }
    }
  }
  if (!root && externalSelection && !absolute) {
    auto found = externalNames.find(head.str());
    if (found != externalNames.end()) {
      if (found->second.size() != 1) {
        types.fail("source.entry",
                   "ambiguous selector name: " + head +
                       "; specify a qualified source name",
                   span);
        return {};
      }
      root = DeclarationId{*found->second.begin()};
      selectedProvider = output.declarations[root->index].module;
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
        selectedProvider = *root;
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
  if (root && selectedProvider) {
    if (provider)
      *provider = selectedProvider;
    if (checkingVisibility &&
        !recordReference(context, *selectedProvider, *root, written, span))
      return {};
  }
  return root;
}
bool Checker::recordReference(const Declaration &owner, DeclarationId provider,
                              DeclarationId target, StringRef written,
                              Span span,
                              std::optional<std::string> abstractModule) {
  if (!types.charge(written.size() + 1 +
                        (abstractModule ? abstractModule->size() : 0),
                    span))
    return false;
  output.api.references.push_back({owner.id, provider, target, span,
                                   written.str(), std::move(abstractModule)});
  return true;
}
bool Checker::retainAPI() {
  auto &records = output.api;
  if (!types.charge(sources.size() + visible.size(), Span{{0}, 0, 0}))
    return false;
  for (unsigned id = 0; id < sources.size(); ++id) {
    const auto &source = *sources[id];
    records.writtenRequirements.push_back(source.explicitRequirements);
    records.writtenEffects.push_back(!source.generated &&
                                     source.effects.has_value());
    for (const auto &[name, binding] : visible[id]) {
      if (!types.charge(name.size() + 1, binding.span))
        return false;
      if (binding.isPublic)
        records.exports.push_back({DeclarationId{id}, binding.target, name,
                                   binding.span, binding.provider.has_value()});
    }
  }
  return true;
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
bool Checker::recover(Error error) {
  auto diagnostic = diagnose(std::move(error));
  if (!diagnostic)
    return false;
  bool resumable = diagnostic->code != "source.limit" &&
                   diagnostic->code != "source.cancelled";
  recoveryDiagnostics->push_back(std::move(*diagnostic));
  return resumable;
}
Expected<std::shared_ptr<const AuthoringStorage>> Checker::retainAnalysis() {
  auto result = std::make_shared<AuthoringStorage>();
  if (!namesReady)
    return std::shared_ptr<const AuthoringStorage>(std::move(result));
  // Existing checks already meter retained types and bodies. Charge the
  // observations copied here, including lookup and reference records.
  uint64_t count = output.declarations.size() + output.api.references.size() +
                   output.lexicalResolutions.size() +
                   output.pendingSpecifications.size();
  for (const auto &scope : visible)
    count += scope.size();
  for (const auto &scope : output.lexicalResolutions)
    count += scope.references.size() + scope.bindings.size();
  if (auto error = work.charge(count))
    return error;
  result->declarations = output.declarations;
  for (unsigned i = 0; i < result->declarations.size(); ++i) {
    bool signature = i < signatureState.size() && signatureState[i] == 2;
    bool body = i < bodyState.size() && bodyState[i] == 2;
    result->signatures.push_back(signature);
    result->bodies.push_back(body);
    // Never retain partially constructed type or execution metadata in a view.
    auto &declaration = result->declarations[i];
    if (!signature) {
      declaration.parameters.clear();
      declaration.inputs.clear();
      declaration.services.clear();
      declaration.inputOrder.clear();
      declaration.outputs.clear();
    }
    if (!body)
      declaration.body.reset();
  }
  result->pendingSpecifications = output.pendingSpecifications;
  result->layoutBodies = output.layoutBodies;
  for (unsigned i = 0; i < result->layoutBodies.size(); ++i)
    if (!result->layoutBodies[i])
      result->layoutBodies[i] = output.layoutHeaders[i];
  result->api = output.api;
  result->lexicalResolutions = output.lexicalResolutions;
  result->names = output.names ? output.names
                               : std::make_shared<NameEnvironment>(
                                     NameEnvironment{modules, visible});
  return std::shared_ptr<const AuthoringStorage>(std::move(result));
}
Error check(std::vector<SyntaxDeclaration> syntax, CheckedStorage &output,
            Work &work, AnalysisStorage *analysis) {
  Checker checker(std::move(syntax), output, work);
  if (analysis)
    checker.recoveryDiagnostics = &analysis->diagnostics;
  auto error = checker.run();
  if (!analysis)
    return error;
  if (error)
    checker.recover(std::move(error));
  auto view = checker.retainAnalysis();
  if (!view)
    return view.takeError();
  analysis->authoring = std::move(*view);
  output.authoring = analysis->authoring;
  return Error::success();
}
} // namespace zkc::language::detail
