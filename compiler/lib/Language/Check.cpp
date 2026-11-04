#include "Checker.h"
#include "CommonRequirements.h"
#include "ScopedWitness.h"
#include "WrittenSource.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Language/Diagnostics.h"
#include <algorithm>
#include <numeric>
using namespace llvm;
namespace zkc::language::detail {
Checker::Checker(std::vector<SyntaxDeclaration> syntax, CheckedStorage &output,
                 Work &work)
    : output(output), work(work),
      types(output.declarations, output.assets, work,
            [this](DeclarationId id) { return signature(id); }),
      syntax(std::move(syntax)) {
  types.completeDispatchBody = [this](DeclarationId id,
                                      unsigned enclosingCalls) {
    auto caller = activeBody;
    if (enclosingCalls >= this->work.limits.callDepth ||
        activeBodyDepth >= this->work.limits.callDepth - enclosingCalls)
      return types.fail("source.limit", "dispatched helper call depth exceeded",
                        this->output.declarations[id.index].span);
    if (!body(id, activeBodyDepth + enclosingCalls + 1))
      return false;
    if (caller)
      bodyHeights[caller->index] =
          std::max(bodyHeights[caller->index],
                   bodyHeights[id.index] + enclosingCalls + 1);
    return true;
  };
}
Checker::Checker(CheckedStorage &output, Work &work, AccessContext policy)
    : Checker({}, output, work) {
  signatureState.assign(output.declarations.size(), 2);
  access = std::move(policy);
  types.completeDispatchBody = {};
}
void Checker::registerContractInference(Declaration &decl,
                                        const SyntaxDeclaration &source) {
  // Rule associations have catalog contracts; installed primitives infer
  // theirs like any primitive declaration.
  if (!source.abstract && !source.explicitRequirements &&
      !index().ruleAssociation(decl.id) &&
      (source.kind == Declaration::Kind::Oracle ||
       source.kind == Declaration::Kind::Math ||
       source.kind == Declaration::Kind::Local ||
       source.kind == Declaration::Kind::EntryFunction ||
       source.kind == Declaration::Kind::DomainFunction ||
       source.kind == Declaration::Kind::Protocol ||
       source.kind == Declaration::Kind::Construction))
    inferredContracts.insert(&decl);
}
void Checker::installContractInference(bool signaturesOnly) {
  auto eligible = [this, signaturesOnly](const Declaration *scope) {
    return inferredContracts.count(scope) &&
           (!signaturesOnly || signatureState[scope->id.index] == 1);
  };
  types.inferCapability = [this, eligible](const Declaration *scope,
                                           const CapabilityBound &bound) {
    if (!eligible(scope))
      return false;
    auto requirement = bound;
    requirement.inferred = true;
    output.declarations[scope->id.index].capabilityBounds.push_back(
        std::move(requirement));
    return true;
  };
  types.inferNatural = [this, eligible](const Declaration &scope,
                                        const NaturalBound &bound) {
    if (!eligible(&scope))
      return false;
    auto requirement = bound;
    requirement.inferred = true;
    output.declarations[scope.id.index].bounds.push_back(
        std::move(requirement));
    return true;
  };
  types.collectUsage =
      [this, eligible](const Declaration &scope, const Type &type, Usage usage,
                       Span span, StringRef code, StringRef message) {
        return eligible(&scope) &&
               collectUsage(scope, type, usage, span, code, message);
      };
}
void Checker::installAdmissionCollection(bool signaturesOnly) {
  // The vector is the checked contract; this pass-local index only coalesces
  // repeated requirements and retains a shortest representative origin chain.
  types.recordAdmission = [this,
                           signaturesOnly](const Declaration &scope,
                                           AdmissionObligation obligation) {
    if (signaturesOnly && signatureState[scope.id.index] != 1)
      return false;
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
}
bool Checker::prepareSignatureReconstruction(DeclarationId id,
                                             const SyntaxDeclaration &source) {
  auto &decl = output.declarations[id.index];
  if (!chargeStaticSignature(decl))
    return false;
  // Keep IDs, namespaces and immutable bodies for semantic queries. Rebuild
  // the whole signature from authored syntax, including inherited contracts.
  decl.kind = source.kind;
  decl.parameters.clear();
  decl.bounds.clear();
  decl.permissionBounds.clear();
  decl.capabilityBounds.clear();
  decl.dataPreconditions.clear();
  for (const auto &obligation : decl.admissions)
    if (!types.chargeType(obligation.type, obligation.span) ||
        !types.charge(obligation.calls.size() + 1, obligation.span))
      return false;
  decl.admissions.clear();
  decl.inputs.clear();
  decl.outputs.clear();
  decl.scopedInputs.clear();
  decl.domainInputs.clear();
  decl.domainResult.reset();
  decl.services.clear();
  decl.fields.clear();
  decl.alternatives.clear();
  decl.placement.reset();
  decl.permissions = source.permissions;
  decl.resource = source.resource;
  decl.sealed = source.sealed;
  decl.associatedSort = source.associatedSort;
  decl.abstract = source.abstract;
  decl.logical = source.logical || (source.kind == Declaration::Kind::Record &&
                                    !source.roles.empty());
  decl.effectAllowance =
      source.effects
          ? std::optional<EffectSummary>(EffectSummary{*source.effects})
          : std::nullopt;
  decl.inputOrder = source.inputOrder;
  decl.implementation.reset();
  if (decl.kind == Declaration::Kind::Associated ||
      decl.kind == Declaration::Kind::Alias)
    decl.domain = {};
  if (decl.kind == Declaration::Kind::Domain) {
    // Domain identities originate in authored headers, too. A mutable alias
    // or installed-domain name cannot become the witness's type authority.
    if (source.assetDomain) {
      auto asset = llvm::find_if(output.assets, [&](const Asset &asset) {
        return asset.name() == source.domain;
      });
      if (asset == output.assets.end())
        return types.fail("source.scoped-witness", "missing authored asset",
                          source.span);
      decl.domain = assetType(source.target == "ring" ? "Ring" : "Bundle",
                              asset->identity());
    } else {
      auto sorts = protocol::domainSorts();
      auto sort = llvm::find_if(sorts, [&](const std::string &sort) {
        return StringRef(sort).lower() == source.target;
      });
      if (sort == sorts.end() ||
          protocol::installedDomains().identitySort(source.domain) != *sort)
        return types.fail("source.scoped-witness", "invalid authored domain",
                          source.span);
      decl.domain = domainType(*sort, source.domain);
    }
  }
  if (reconstructedSources.empty()) {
    installContractInference(/*signaturesOnly=*/true);
    installAdmissionCollection(/*signaturesOnly=*/true);
  }
  registerContractInference(decl, source);
  auto &written = reconstructedSources[id.index];
  // Body trees and nested declarations are not part of a signature replay.
  written.kind = source.kind;
  written.name = source.name;
  written.span = source.span;
  written.roles = source.roles;
  written.fields = source.fields;
  written.alternatives = source.alternatives;
  written.oracleShapes = source.oracleShapes;
  written.parameters = source.parameters;
  written.requirements = source.requirements;
  written.explicitRequirements = source.explicitRequirements;
  written.inputs = source.inputs;
  written.outputs = source.outputs;
  written.scopedInputs = source.scopedInputs;
  written.domainInputs = source.domainInputs;
  written.domainResult = source.domainResult;
  written.services = source.services;
  written.effects = source.effects;
  written.effectDependencies = source.effectDependencies;
  written.definition = source.definition;
  written.associatedSort = source.associatedSort;
  written.permissions = source.permissions;
  written.resource = source.resource;
  written.sealed = source.sealed;
  written.abstract = source.abstract;
  sources.resize(output.declarations.size());
  sources[id.index] = &written;
  signatureState[id.index] = 0;
  return true;
}
Error Checker::run() {
  Work::Scope phase(work, SourceWorkPhase::Declarations);
  if (auto error = checkCapabilityInstallation())
    return error;
  phase.enter(SourceWorkPhase::WrittenRetention);
  auto written = retainWrittenHeaders(syntax, work);
  if (!written)
    return written.takeError();
  phase.enter(SourceWorkPhase::Declarations);
  if (auto error = expandLayoutSections(syntax, work))
    return error;
  if (!collect() || !imports() || !indexDeclarations() || !classifyServices() ||
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
  phase.enter(SourceWorkPhase::Parsing);
  for (unsigned i = 0; i < bodyScopes.size(); ++i) {
    auto error = output.layoutHeaders[i]
                     ? parseLayoutBodies(SourceId{i}, bodyScopes[i], output,
                                         work, recoveryDiagnostics)
                     : parseBodies((*output.sources)[i], SourceId{i},
                                   output.tokens[i], bodyScopes[i], work);
    if (error)
      return error;
  }
  phase.enter(SourceWorkPhase::Declarations);
  if (!prepareOraclePredicates() || !layoutSpecifications())
    return types.takeError();
  if (!recoveryDiagnostics || recoveryDiagnostics->empty()) {
    Work::Scope writtenPhase(work, SourceWorkPhase::WrittenRetention);
    if (auto error = retainWrittenBodies(**written, sources, work))
      return error;
    output.writtenSources = std::move(*written);
  }
  for (auto &decl : output.declarations)
    registerContractInference(decl, *sources[decl.id.index]);
  installContractInference(/*signaturesOnly=*/false);
  installAdmissionCollection(/*signaturesOnly=*/false);
  phase.enter(SourceWorkPhase::Signatures);
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
  if (!checkInstalledSignatures() || !prepareOperators())
    return types.takeError();
  if (!relationIdentities())
    return types.takeError();
  if (!pendingClaimRelations())
    return types.takeError();
  bodyState.resize(output.declarations.size());
  bodyHeights.resize(bodyState.size());
  phase.enter(SourceWorkPhase::Conformance);
  for (auto &decl : output.declarations)
    if (decl.kind == Declaration::Kind::Module && decl.implementation &&
        !conformance(decl.id))
      return types.takeError();
  phase.enter(SourceWorkPhase::Representations);
  if (!representations())
    return types.takeError();
  phase.enter(SourceWorkPhase::Permissions);
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
  phase.enter(SourceWorkPhase::Bodies);
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
  phase.enter(SourceWorkPhase::CommonInputs);
  if (auto error = checkCommonControlRequirements(output.declarations,
                                                  output.assets, work))
    return error;
  phase.enter(SourceWorkPhase::EntriesAndClaims);
  if (!constructions() || !entries() || !sourceClaims())
    return types.takeError();
  inferredContracts.clear();
  types.inferCapability = {};
  types.inferNatural = {};
  types.collectUsage = {};
  types.recordAdmission = {};
  phase.enter(SourceWorkPhase::RetainedViews);
  if (!retainAPI() || !retainNotations() || !retainScopedSources())
    return types.takeError();
  output.authoredReferences =
      std::make_shared<const std::vector<ReferenceRecord>>(
          output.api.references);
  phase.enter(SourceWorkPhase::ScopedSources);
  if (auto error = checkScopedSources(output, work))
    return error;
  // The scoped witness check re-resolves but records nothing, so every
  // recorded route is final here.
  phase.enter(SourceWorkPhase::SourceAuthorities);
  return computeSourceAuthorities(output, assetDomains, work);
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
  auto selected =
      index().scopeBinding(accessFor(decl), name, lookupTraversal(span));
  if (std::holds_alternative<ResolvedReference>(selected))
    return types.fail("source.shadow", "binding shadows a visible declaration",
                      span);
  return acceptFailure(std::get<LookupFailure>(selected), span, false);
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
    decl.logical =
        source.logical ||
        (source.kind == Declaration::Kind::Record && !source.roles.empty());
    decl.sealed = source.sealed;
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
    if (!formingIndex->add(decl,
                           (*output.sources)[decl.span.source.index].origin))
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
      assetDomains.emplace(decl.id.index, found - output.assets.begin());
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
    if (decl.kind == Declaration::Kind::Module) {
      moduleIds.push_back(id);
      module = id;
    }
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
    auto found = formingIndex->canonical(root.name);
    if (!found ||
        output.declarations[found->index].kind != Declaration::Kind::Module)
      return types.fail("source.module",
                        "captured child needs an external module declaration",
                        root.span);
  }
  return true;
}
bool Checker::acceptFailure(const LookupFailure &failure, Span span,
                            bool required) {
  if (types.diagnostic)
    return false;
  switch (failure.kind) {
  case LookupFailureKind::NotFound:
    if (!required)
      return true;
    return types.fail("source.name", "unknown declaration: " + failure.segment,
                      span);
  case LookupFailureKind::Inaccessible:
    return types.fail(
        "source.private",
        "cannot reference private declaration: " + failure.segment, span,
        failure.definition ? std::vector<Span>{*failure.definition}
                           : std::vector<Span>{});
  case LookupFailureKind::Ambiguous:
    return types.fail("source.entry",
                      "ambiguous selector name: " + failure.segment, span);
  case LookupFailureKind::Cycle:
    return types.fail("source.cycle", "cyclic import bindings", span);
  case LookupFailureKind::Limit:
    return types.fail("source.limit", "declaration lookup work limit", span);
  case LookupFailureKind::WrongCategory:
    return types.fail("source.name",
                      "selected declaration has the wrong category", span);
  }
  llvm_unreachable("unknown lookup failure");
}
LookupTraversal Checker::lookupTraversal(Span span) {
  LookupTraversal result{[this, span] { return types.charge(1, span); }, {}};
  if (loadBinding)
    result.load = [this](DeclarationId owner,
                         StringRef name) -> std::optional<LookupFailure> {
      if (loadBinding(owner, name))
        return {};
      // Preserve the binding loader's diagnostic, including cancellation and
      // conflicts; do not relabel a failed work charge as an import cycle.
      auto kind = LookupFailureKind::WrongCategory;
      if (types.diagnostic) {
        if (types.diagnostic->code == "source.limit" ||
            types.diagnostic->code == "source.cancelled")
          kind = LookupFailureKind::Limit;
        else if (types.diagnostic->code == "source.cycle")
          kind = LookupFailureKind::Cycle;
      }
      return LookupFailure{kind, owner, name.str()};
    };
  return result;
}
std::optional<ResolvedReference> Checker::select(const Declaration &context,
                                                 StringRef name, Span span,
                                                 bool required) {
  auto result = index().lookup(accessFor(context), name, lookupTraversal(span));
  if (auto *ref = std::get_if<ResolvedReference>(&result))
    return *ref;
  acceptFailure(std::get<LookupFailure>(result), span, required);
  return {};
}
std::optional<DeclarationId> Checker::member(const Declaration &context,
                                             DeclarationId owner,
                                             StringRef name, Span span) {
  auto result =
      index().member(accessFor(context), owner, name, lookupTraversal(span));
  if (auto *ref = std::get_if<ResolvedReference>(&result))
    return ref->target;
  acceptFailure(std::get<LookupFailure>(result), span, false);
  return {};
}
std::optional<DeclarationId> Checker::resolve(const Declaration &context,
                                              StringRef name, Span span,
                                              bool required) {
  auto ref = select(context, name, span, required);
  if (!ref)
    return {};
  if (referenceSite)
    typeReferences.insert_or_assign(referenceSite, *ref);
  if (!recordReference(context, ReferenceRoute::Path, *ref, name, span))
    return {};
  return ref->target;
}
std::optional<DeclarationId>
Checker::probe(const Declaration &context, StringRef name, Span span,
               std::optional<DeclarationId> *provider) {
  auto ref = select(context, name, span, false);
  if (!ref)
    return {};
  if (provider)
    *provider = ref->provider;
  return ref->target;
}
bool Checker::recordReference(const Declaration &owner, ReferenceRoute route,
                              const ResolvedReference &reference,
                              StringRef written, Span span, uint32_t ordinal) {
  if (!referencesReady || (replayedOwner && *replayedOwner == owner.id.index))
    return true;
  if (!types.charge(written.size() + reference.path.size() + 1, span))
    return false;
  const auto &site =
      referenceSite ? referenceSite : sources[owner.id.index]->referenceSite;
  auto [node, inserted] = referenceNodes.emplace(
      site, ReferenceNodeId{uint32_t(referenceNodes.size())});
  auto key = std::make_tuple(owner.id.index, node->second.index, route,
                             written.str(), ordinal);
  if (auto at = recordedReferences.find(key); at != recordedReferences.end()) {
    return output.api.references[at->second].reference == reference ||
           types.fail("source.binding-witness",
                      "one authored reference selected different routes", span);
  }
  recordedReferences.emplace(std::move(key), output.api.references.size());
  output.api.references.push_back(
      {owner.id,
       reference.provider,
       reference.target,
       span,
       written.str(),
       reference.abstract && reference.abstract->module.symbolic
           ? std::optional(formatType(reference.abstract->module))
           : std::nullopt,
       route,
       reference,
       {node->second, route, written.str(), ordinal}});
  return true;
}
bool Checker::retainAPI() {
  auto &records = output.api;
  if (!types.charge(sources.size() + index().bindingCount(), Span{{0}, 0, 0}))
    return false;
  for (unsigned id = 0; id < sources.size(); ++id) {
    const auto &source = *sources[id];
    records.writtenRequirements.push_back(source.explicitRequirements);
    records.writtenEffects.push_back(!source.generated &&
                                     source.effects.has_value());
    for (const auto &[name, binding] : index().bindings(DeclarationId{id})) {
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
  auto result = roleArguments(decl, names, span);
  if (!result)
    return {};
  if (result->empty()) {
    types.fail("source.roles", "role set must be nonempty and distinct", span);
    return {};
  }
  llvm::sort(*result);
  return result;
}
std::optional<std::vector<unsigned>>
Checker::roleArguments(const Declaration &decl, ArrayRef<std::string> names,
                       Span span) {
  if (!types.charge(names.size() * (decl.roles.size() + names.size() + 1),
                    span))
    return {};
  std::vector<unsigned> result;
  for (auto &name : names) {
    auto found = llvm::find(decl.roles, name);
    if (found == decl.roles.end()) {
      types.fail("source.roles", "unknown participant: " + name, span);
      return {};
    }
    unsigned role = found - decl.roles.begin();
    if (llvm::is_contained(result, role)) {
      types.fail("source.roles", "participant substitution must be injective",
                 span);
      return {};
    }
    result.push_back(role);
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
  count += index().bindingCount();
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
  result->declarationIndex = output.declarationIndex;
  result->api = output.api;
  result->lexicalResolutions = output.lexicalResolutions;
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
  Work::Scope retained(work, SourceWorkPhase::RetainedViews);
  auto view = checker.retainAnalysis();
  if (!view)
    return view.takeError();
  analysis->authoring = std::move(*view);
  output.authoring = analysis->authoring;
  return Error::success();
}
} // namespace zkc::language::detail
