#include "SignatureWitness.h"
#include "Checker.h"
#include "Effects.h"
#include "Internal.h"
#include "ScopedWitness.h"
#include "WrittenSource.h"
#include "zkc/Language/Builtins.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
namespace {
bool checkOrigins(Semantics &types, const Declaration &decl,
                  const SyntaxDeclaration &source,
                  const ScopedParameter &parameter,
                  const SyntaxScopedSignature &written) {
  auto refuse = [&](llvm::StringRef message) {
    return types.fail("source.scoped-witness", message, parameter.span);
  };
  const auto &signature = parameter.signature;
  if (!types.charge(written.inputLabels.size() + source.domainInputs.size() +
                        written.itemOrigins.size() +
                        parameter.itemOrigins.size() + 1,
                    parameter.span))
    return false;
  if (written.inputLabels.size() != signature.inputs.size() ||
      written.inputLabels != parameter.inputLabels ||
      source.domainInputs.size() != decl.domainInputs.size())
    return refuse("callback source input coverage differs");
  std::map<std::string, unsigned> labels, domains;
  for (unsigned i = 0; i < written.inputLabels.size(); ++i) {
    const auto &label = written.inputLabels[i];
    if (!types.charge(label.size() + 1, parameter.span))
      return false;
    if (!label.empty() && !labels.emplace(label, i).second)
      return refuse("duplicate callback source label");
  }
  for (unsigned i = 0; i < source.domainInputs.size(); ++i) {
    const auto &name = source.domainInputs[i].name;
    if (!types.charge(name.size() + 1, parameter.span))
      return false;
    if (name != decl.domainInputs[i].name || !domains.emplace(name, i).second)
      return refuse("callback source domain differs");
  }
  std::map<unsigned, unsigned> expected;
  for (const auto &condition : written.itemOrigins) {
    if (!types.charge(condition.input.size() + condition.domain.size() + 1,
                      condition.span))
      return false;
    auto input = labels.find(condition.input);
    auto domain = domains.find(condition.domain);
    if (input == labels.end() || domain == domains.end() ||
        signature.inputs[input->second] !=
            decl.domainInputs[domain->second].item ||
        !expected.emplace(input->second, domain->second).second)
      return refuse("invalid authored callback item origin");
  }
  return parameter.itemOrigins == expected ||
         refuse("callback item origins differ from authored selectors");
}

bool checkMemberInputs(Semantics &types, const Declaration &required,
                       const Declaration &provided,
                       const Substitution &bindings) {
  auto refuse = [&] {
    return types.fail("source.scoped-witness",
                      "implementation callback contract differs from interface",
                      provided.span);
  };
  if (!types.charge(required.inputOrder.size() + required.domainInputs.size() +
                        required.scopedInputs.size() + 1,
                    provided.span))
    return false;
  if (required.kind != provided.kind ||
      required.inputOrder.size() != provided.inputOrder.size() ||
      required.domainInputs.size() != provided.domainInputs.size() ||
      required.scopedInputs.size() != provided.scopedInputs.size())
    return refuse();
  for (unsigned i = 0; i < required.inputOrder.size(); ++i)
    if (required.inputOrder[i].kind != provided.inputOrder[i].kind ||
        required.inputOrder[i].index != provided.inputOrder[i].index)
      return refuse();
  auto sameType = [&](const Type &expected, const Type &actual) {
    auto resolved = types.substitute(expected, bindings, provided.span);
    return resolved && (*resolved == actual || refuse());
  };
  for (unsigned i = 0; i < required.domainInputs.size(); ++i)
    if (!sameType(required.domainInputs[i].item, provided.domainInputs[i].item))
      return false;
  for (unsigned i = 0; i < required.scopedInputs.size(); ++i) {
    const auto &expected = required.scopedInputs[i];
    const auto &actual = provided.scopedInputs[i];
    if (!types.charge(expected.itemOrigins.size() + actual.itemOrigins.size() +
                          expected.signature.inputs.size() + 1,
                      provided.span))
      return false;
    if (expected.itemOrigins != actual.itemOrigins ||
        expected.signature.mode != actual.signature.mode ||
        expected.signature.allowance != actual.signature.allowance ||
        expected.signature.inputs.size() != actual.signature.inputs.size())
      return refuse();
    for (unsigned j = 0; j < expected.signature.inputs.size(); ++j)
      if (!sameType(expected.signature.inputs[j], actual.signature.inputs[j]))
        return false;
    if (!sameType(expected.signature.result, actual.signature.result))
      return false;
  }
  return true;
}
} // namespace
llvm::Error checkSignatureSources(const CheckedStorage &storage, Work &work) {
  Semantics types(storage.declarations, storage.assets, work);
  size_t retained = 0;
  for (const auto &decl : storage.declarations) {
    if (!types.charge(1, decl.span))
      return types.takeError();
    auto found = storage.signatureSources.find(decl.id.index);
    if (found == storage.signatureSources.end()) {
      if (!decl.scopedInputs.empty() || decl.effectAllowance)
        return failure("source.scoped-witness", "missing signature source",
                       decl.span);
      continue;
    }
    ++retained;
    auto refuse = [&] {
      return failure("source.scoped-witness",
                     "contract differs from authored signature", decl.span);
    };
    if (!found->second)
      return refuse();
    const auto &source = *found->second;
    if (!types.charge(source.scopedInputs.size() +
                          source.effectDependencies.size() + 1,
                      decl.span))
      return types.takeError();
    if (decl.scopedInputs.size() != source.scopedInputs.size())
      return refuse();
    for (unsigned slot = 0; slot < decl.scopedInputs.size(); ++slot) {
      const auto &written = source.scopedInputs[slot].scoped;
      const auto &parameter = decl.scopedInputs[slot];
      if (!written || written->mode != parameter.signature.mode ||
          written->allowance != parameter.signature.allowance)
        return refuse();
      if (!checkOrigins(types, decl, source, parameter, *written))
        return types.takeError();
    }
    std::optional<EffectSummary> expected;
    if (source.effects) {
      expected = EffectSummary{*source.effects};
      for (const auto &name : source.effectDependencies) {
        if (!types.charge(source.scopedInputs.size() + 1, decl.span))
          return types.takeError();
        auto input = llvm::find_if(source.scopedInputs, [&](const auto &port) {
          return port.name == name;
        });
        if (input == source.scopedInputs.end() || !input->scoped)
          return refuse();
        expected->dependencies.emplace(
            unsigned(input - source.scopedInputs.begin()),
            input->scoped->allowance);
      }
      if (!joinEffects(types, *expected, EffectSummary{}, decl.span))
        return types.takeError();
    }
    if (expected != decl.effectAllowance)
      return refuse();
  }
  if (retained != storage.signatureSources.size())
    return failure("source.scoped-witness", "invalid signature source owner");
  return llvm::Error::success();
}
namespace {
// The expected edges come from immutable authored headers and frozen canonical
// IDs, not the mutable Declaration::members or conformance vectors.
struct ContractHeaders {
  const CheckedStorage &storage;
  Semantics &types;
  std::map<uint32_t, const SyntaxDeclaration *> sources;
  std::map<uint32_t, uint32_t> parents;
  bool managed = false;
  bool collect(const SyntaxDeclaration &source, const std::string &path,
               std::optional<DeclarationId> parent, unsigned depth) {
    if (depth > types.work.limits.typeDepth)
      return types.fail("source.limit", "conformance source depth",
                        source.span);
    if (!types.charge(path.size() + source.members.size() + 1, source.span))
      return false;
    if (source.anonymous || source.generated)
      return true;
    if (source.kind != Declaration::Kind::Module &&
        source.kind != Declaration::Kind::Interface &&
        source.kind != Declaration::Kind::Associated &&
        source.kind != Declaration::Kind::Alias &&
        source.kind != Declaration::Kind::Domain &&
        source.kind != Declaration::Kind::Record &&
        source.kind != Declaration::Kind::Variant &&
        source.kind != Declaration::Kind::Math &&
        source.kind != Declaration::Kind::Local &&
        (!managed || source.kind != Declaration::Kind::Protocol) &&
        source.kind != Declaration::Kind::DomainFunction)
      return true;
    auto id = storage.declarationIndex->canonical(path);
    if (!id || id->index >= storage.declarations.size())
      return types.fail("source.scoped-witness", "missing authored declaration",
                        source.span);
    // An external child link has no signature; its captured file supplies it.
    if (source.externalModule)
      return true;
    if (!sources.emplace(id->index, &source).second)
      return types.fail("source.scoped-witness", "duplicate authored header",
                        source.span);
    if (!parent && StringRef(path).contains("::"))
      parent = storage.declarationIndex->canonical(
          StringRef(path).rsplit("::").first);
    if (parent)
      parents.emplace(id->index, parent->index);
    for (const auto &member : source.members)
      if (!collect(member, path + "::" + member.name, *id, depth + 1))
        return false;
    return true;
  }
};
bool reconstructInferredResult(Semantics &types, const CheckedStorage &storage,
                               const SyntaxDeclaration &source,
                               Declaration &written) {
  if (!source.outputs.empty() || source.abstract ||
      (source.kind != Declaration::Kind::Math &&
       source.kind != Declaration::Kind::Local))
    return true;
  auto refuse = [&] {
    return types.fail("source.scoped-witness",
                      "inferred result differs from checked source body",
                      source.span);
  };
  if (!types.charge(1, source.span))
    return false;
  const auto &actual = storage.declarations[written.id.index];
  auto retained = storage.bodySources.find(written.id.index);
  if (retained == storage.bodySources.end() || !retained->second ||
      retained->second->owner.index != written.id.index ||
      !retained->second->syntax || !actual.body)
    return refuse();
  const auto &syntax = *retained->second->syntax;
  const auto &body = *actual.body;
  if (syntax.kind != source.kind || syntax.name != source.name ||
      syntax.abstract || !syntax.outputs.empty() || syntax.bodies.empty() ||
      syntax.span.source.index != source.span.source.index ||
      syntax.span.begin != source.span.begin ||
      syntax.span.end != source.span.end || body.stopped ||
      body.mode != (source.kind == Declaration::Kind::Math ? Body::Mode::Math
                                                           : Body::Mode::Local))
    return refuse();
  const auto &region = syntax.bodies.front();
  if (!types.charge(region.results.size() + body.results.size() + 1,
                    region.span))
    return false;
  if (!region.returned || region.results.size() != 1 ||
      body.results.size() != 1 ||
      region.results.front().second >= syntax.expressions.size())
    return refuse();
  auto value = body.expressionValues.find(region.results.front().second);
  if (value == body.expressionValues.end() ||
      value->second.index != body.results.front().index ||
      value->second.index >= body.values.size())
    return refuse();
  // An omitted annotation authorizes body result inference, independently of
  // whether precondition inference is allowed. The result type comes from the
  // immutable checked Body, never Declaration::outputs or the interface. The
  // surrounding scoped witness checks the source/SSA graph with its existing
  // body witnesses; here we additionally bind its return to the authored tail.
  const auto &type = body.values[value->second.index].type;
  if (!types.chargeType(type, region.span))
    return false;
  written.outputs.push_back({"result", type, {}, region.span});
  return true;
}
bool signatureAgrees(Semantics &types, const Declaration &actual,
                     const Declaration &written, bool permitsInference) {
  auto refuse = [&] {
    return types.fail("source.scoped-witness",
                      "conformance signature differs from authored header",
                      actual.span);
  };
  if (!types.charge(actual.parameters.size() + actual.inputs.size() +
                        actual.outputs.size() + actual.bounds.size() +
                        actual.permissionBounds.size() +
                        actual.capabilityBounds.size() + 1,
                    actual.span))
    return false;
  if (actual.kind != written.kind || actual.abstract != written.abstract ||
      actual.associatedSort != written.associatedSort ||
      !(actual.permissions == written.permissions) ||
      actual.resource != written.resource || actual.sealed != written.sealed ||
      actual.domain != written.domain ||
      actual.implementation != written.implementation ||
      actual.parameters.size() != written.parameters.size() ||
      actual.inputs.size() != written.inputs.size() ||
      actual.outputs.size() != written.outputs.size() ||
      actual.domainResult != written.domainResult ||
      actual.dataPreconditions != written.dataPreconditions)
    return refuse();
  for (unsigned i = 0; i < actual.parameters.size(); ++i) {
    const auto &a = actual.parameters[i], &b = written.parameters[i];
    if (a.name != b.name || a.atom != b.atom || a.sort != b.sort ||
        a.domainSort != b.domainSort || a.arguments != b.arguments ||
        bool(a.interface) != bool(b.interface) ||
        (a.interface && a.interface->index != b.interface->index) ||
        !(a.permissions == b.permissions))
      return refuse();
  }
  for (bool input : {true, false}) {
    const auto &a = input ? actual.inputs : actual.outputs;
    const auto &b = input ? written.inputs : written.outputs;
    for (unsigned i = 0; i < a.size(); ++i)
      if (a[i].name != b[i].name || a[i].type != b[i].type)
        return refuse();
  }
  if (!checkMemberInputs(types, written, actual, {}))
    return false;
  // Replay includes signature inference, not just written bounds. Bodies can
  // append obligations (or strengthen an inferred usage leaf) only where the
  // authored declaration permits inference. Such additions are goals below,
  // never assumptions. Modules, interfaces and abstract/explicit contracts
  // must match the independently reconstructed product exactly.
  auto boundsAgree = [&](const auto &candidate, const auto &expected,
                         auto agrees) {
    if (candidate.size() < expected.size())
      return false;
    for (unsigned i = 0; i < expected.size(); ++i)
      if (candidate[i].inferred != expected[i].inferred ||
          !agrees(candidate[i], expected[i]))
        return false;
    for (unsigned i = expected.size(); i < candidate.size(); ++i)
      if (!permitsInference || !candidate[i].inferred)
        return false;
    return true;
  };
  if (!boundsAgree(actual.bounds, written.bounds,
                   [](const auto &a, const auto &b) {
                     return a.lhs == b.lhs && a.rhs == b.rhs;
                   }) ||
      !boundsAgree(actual.permissionBounds, written.permissionBounds,
                   [&](const auto &a, const auto &b) {
                     return a.type == b.type &&
                            (permitsInference && b.inferred
                                 ? a.permissions.includes(b.permissions)
                                 : a.permissions == b.permissions);
                   }) ||
      !boundsAgree(actual.capabilityBounds, written.capabilityBounds,
                   [](const auto &a, const auto &b) {
                     return a.predicate == b.predicate &&
                            a.arguments == b.arguments;
                   }))
    return refuse();
  // Defined Local effects may be inferred from their independently checked
  // body. Explicit and abstract ceilings must equal the authored ceiling.
  if ((written.effectAllowance || actual.abstract) &&
      actual.effectAllowance != written.effectAllowance)
    return refuse();
  return true;
}
// Permission caches in a candidate obligation are not premises, including
// caches nested in a product. The caller charges and bounds the tree first.
void clearPermissionAssumptions(Type &type) {
  type.assumptions = {};
  for (auto &argument : type.arguments)
    clearPermissionAssumptions(argument);
}
bool implementationAgrees(Semantics &types, const Declaration &module,
                          const Declaration &interface,
                          const Declaration &required,
                          const Declaration &provided,
                          const Substitution &bindings) {
  auto refuse = [&](StringRef message) {
    return types.fail("source.scoped-witness", message, provided.span);
  };
  if (required.kind == Declaration::Kind::Associated) {
    const auto &sort = required.associatedSort;
    if (isDomainSort(sort) && (sort != provided.associatedSort ||
                               sort != domainSort(provided.domain)))
      return refuse("associated implementation sort differs");
    if (isStaticOnly(provided.domain))
      return isDomainSort(sort) ||
             refuse("runtime associated representation differs");
    Type self(Type::Kind::Module, module.qualifiedName);
    for (const auto &p : module.parameters)
      self.arguments.push_back(parameterType(p));
    Type type(Type::Kind::Associated, provided.qualifiedName);
    type.arguments.push_back(std::move(self));
    auto promised = required.permissions.value_or(Permissions{});
    if (required.resource)
      promised = {false, *required.resource == Resource::Affine};
    auto caps = types.permissions(type, provided.span, &module);
    return caps && (caps->includes(promised) ||
                    refuse("associated implementation permissions differ"));
  }
  if (required.parameters.size() != interface.parameters.size() ||
      provided.parameters.size() != module.parameters.size() ||
      required.inputs.size() != provided.inputs.size() ||
      required.outputs.size() != provided.outputs.size() ||
      bool(required.domainResult) != bool(provided.domainResult))
    return refuse("implementation signature arity differs");
  for (bool input : {true, false}) {
    const auto &a = input ? required.inputs : required.outputs;
    const auto &b = input ? provided.inputs : provided.outputs;
    for (unsigned i = 0; i < a.size(); ++i) {
      auto expected = types.substitute(a[i].type, bindings, provided.span);
      if (!expected || (*expected != b[i].type &&
                        !refuse("implementation port signature differs")))
        return false;
    }
  }
  if (!checkMemberInputs(types, required, provided, bindings))
    return false;
  if (required.domainResult) {
    auto expected =
        types.substitute(*required.domainResult, bindings, provided.span);
    if (!expected || (*expected != *provided.domainResult &&
                      !refuse("implementation domain result differs")))
      return false;
  }
  for (const auto &condition : provided.dataPreconditions)
    if (!llvm::is_contained(required.dataPreconditions, condition))
      return refuse("implementation strengthens data preconditions");
  Declaration available{};
  available.parameters = module.parameters;
  available.bounds = module.bounds;
  available.permissionBounds = module.permissionBounds;
  available.capabilityBounds = module.capabilityBounds;
  for (const auto &p : required.parameters) {
    auto actual = bindings.find(p.atom);
    if (actual != bindings.end() && !(p.permissions == Permissions{}))
      available.permissionBounds.push_back(
          {actual->second, p.permissions, p.span});
  }
  for (const auto &bound : required.bounds) {
    Type l(Type::Kind::Natural), r(Type::Kind::Natural);
    l.dimension = bound.lhs;
    r.dimension = bound.rhs;
    auto lhs = types.substitute(l, bindings, provided.span);
    auto rhs = types.substitute(r, bindings, provided.span);
    if (!lhs || !rhs)
      return false;
    available.bounds.push_back({lhs->dimension, rhs->dimension, bound.span});
  }
  for (const auto &bound : required.permissionBounds) {
    auto value = types.substitute(bound.type, bindings, provided.span);
    if (!value)
      return false;
    available.permissionBounds.push_back(
        {*value, bound.permissions, bound.span});
  }
  for (const auto &bound : required.capabilityBounds) {
    CapabilityBound assumption{bound.predicate, {}, bound.span};
    for (const auto &argument : bound.arguments) {
      auto value = types.substitute(argument, bindings, provided.span);
      if (!value)
        return false;
      assumption.arguments.push_back(std::move(*value));
    }
    if (llvm::any_of(assumption.arguments,
                     [&](const auto &t) { return types.symbolic(t); }))
      available.capabilityBounds.push_back(std::move(assumption));
    else if (!types.entails(nullptr, assumption, "source.scoped-witness"))
      return false;
  }
  for (const auto &bound : provided.capabilityBounds)
    if (!types.entails(&available, bound, "source.scoped-witness"))
      return false;
  for (const auto &bound : provided.bounds)
    if (!types.assumptions(available, bound, {}, provided.span))
      return false;
  for (const auto &bound : provided.permissionBounds) {
    if (!types.chargeType(bound.type, provided.span))
      return false;
    Type requirement = bound.type;
    clearPermissionAssumptions(requirement);
    auto value = types.substitute(requirement, {}, provided.span);
    auto caps = value ? types.permissions(*value, provided.span, &available)
                      : std::nullopt;
    if (!caps ||
        (!caps->includes(bound.permissions) &&
         !refuse("implementation strengthens permission preconditions")))
      return false;
  }
  for (unsigned i = 0; i < provided.parameters.size(); ++i) {
    if (isStaticOnly(parameterType(provided.parameters[i])))
      continue;
    auto caps = types.permissions(parameterType(module.parameters[i]),
                                  provided.span, &available);
    if (!caps || (!caps->includes(provided.parameters[i].permissions) &&
                  !refuse("implementation strengthens parameter permissions")))
      return false;
  }
  if (required.kind == Declaration::Kind::DomainFunction)
    return bool(provided.domainDefinition) ||
           refuse("implementation domain recipe missing");
  return provided.body &&
         effectsWithin(types, provided.body->effects,
                       required.effectAllowance.value_or(EffectSummary{}),
                       provided.span);
}
} // namespace
llvm::Expected<std::map<uint32_t, std::vector<ServicePort>>>
replayServicePorts(const CheckedStorage &storage, Work &work) {
  std::map<uint32_t, std::vector<ServicePort>> ports;
  bool needed = false;
  for (const auto &[id, source] : storage.bodySources) {
    if (auto error = work.charge(1, {}))
      return std::move(error);
    if (!source || !source->syntax)
      return failure("source.binding-witness", "missing body source syntax");
    needed |= !source->syntax->services.empty();
  }
  if (!needed)
    return ports;
  Semantics types(storage.declarations, storage.assets, work);
  if (!storage.writtenSources || !storage.declarationIndex)
    return failure("source.binding-witness", "missing managed input headers");
  uint64_t tokens = 0;
  for (const auto &source : storage.tokens)
    tokens += source.size();
  if (!types.charge(tokens, {}))
    return types.takeError();
  auto authored = storage.writtenSources->modules;
  if (auto error = expandLayoutSections(authored, work))
    return std::move(error);
  ContractHeaders headers{storage, types, {}, {}, true};
  for (const auto &source : authored)
    if (!headers.collect(source, source.name, {}, 1))
      return types.takeError();
  // The retained body syntax owns the classification and lexical input IDs.
  // Its type terms and roles are replayed; candidate fields are discarded.
  for (auto &[id, source] : headers.sources) {
    if (source->kind != Declaration::Kind::Protocol)
      continue;
    auto found = storage.bodySources.find(id);
    if (found == storage.bodySources.end() || !found->second ||
        !found->second->syntax)
      return failure("source.binding-witness", "missing managed input syntax",
                     source->span);
    source = found->second->syntax.get();
    for (const auto &port : source->services) {
      auto selected = storage.declarationIndex->lookup(
          SourceAccess{DeclarationId{id}}, port.type.name,
          {[&] { return types.charge(1, port.span); }, {}});
      auto *reference = std::get_if<ResolvedReference>(&selected);
      if (!reference || !port.serviceReference ||
          *reference != *port.serviceReference)
        return types.diagnostic
                   ? types.takeError()
                   : failure("source.binding-witness",
                             "managed constructor lookup differs", port.span);
    }
  }
  if (auto error = chargeSemanticIndex(storage.declarations, work))
    return std::move(error);
  CheckedStorage replay(storage.capture, storage.installation);
  replay.declarations = storage.declarations;
  replay.assets = storage.assets;
  replay.sources = storage.sources;
  replay.declarationIndex = storage.declarationIndex;
  Checker reader(replay, work, SourceAccess{{0}});
  // Shared signature reconstruction must assign parameter indices from the
  // immutable header before substituting service fields and static terms.
  // Service replay deliberately has no separate parameter-indexing authority.
  for (const auto &[id, source] : headers.sources)
    if (!reader.prepareSignatureReconstruction(DeclarationId{id}, *source))
      return reader.types.takeError();
  for (const auto &[id, source] : headers.sources) {
    if (!reader.reconstructSignature(DeclarationId{id}))
      return reader.types.takeError();
    if (source->kind == Declaration::Kind::Protocol)
      ports.emplace(id, replay.declarations[id].services);
  }
  return ports;
}
llvm::Error checkModuleContracts(const CheckedStorage &storage, Work &work) {
  if (!storage.sources || !storage.declarationIndex)
    return failure("source.scoped-witness",
                   "invalid conformance source context");
  for (unsigned i = 0; i < storage.declarations.size(); ++i) {
    const auto &decl = storage.declarations[i];
    if (auto error = work.charge(decl.members.size() + 1, decl.span))
      return error;
    if (decl.id.index != i ||
        decl.span.source.index >= storage.sources->size() ||
        decl.module.index >= storage.declarations.size() ||
        (decl.parent && decl.parent->index >= storage.declarations.size()) ||
        llvm::any_of(decl.members, [&](auto id) {
          return id.index >= storage.declarations.size();
        }))
      return failure("source.scoped-witness",
                     "invalid conformance declaration identity", decl.span);
  }
  Semantics types(storage.declarations, storage.assets, work);
  auto verify = [&]() -> bool {
    if (!storage.writtenSources || !storage.declarationIndex)
      return types.fail("source.scoped-witness",
                        "missing conformance source headers", {});
    bool needsConformance =
        llvm::any_of(storage.declarations, [](const auto &decl) {
          return decl.implementation || !decl.conformance.empty();
        });
    std::function<bool(const SyntaxDeclaration &)> findImplementation =
        [&](const SyntaxDeclaration &source) {
          if (!types.charge(1, source.span))
            return false;
          needsConformance |= source.kind == Declaration::Kind::Module &&
                              source.definition.has_value();
          for (const auto &child : source.members)
            if (!findImplementation(child))
              return false;
          return true;
        };
    for (const auto &source : storage.writtenSources->modules)
      if (!findImplementation(source))
        return false;
    if (!needsConformance)
      return true;
    // Use the same section expansion on an independent authored snapshot;
    // written parameter groups do not create declaration namespaces.
    uint64_t tokens = 0;
    for (const auto &source : storage.tokens)
      tokens += source.size();
    if (!types.charge(tokens, {}))
      return false;
    auto authored = storage.writtenSources->modules;
    if (auto error = expandLayoutSections(authored, work))
      return types.accept(std::move(error));
    ContractHeaders headers{storage, types, {}, {}};
    for (const auto &source : authored)
      if (!headers.collect(source, source.name, {}, 1))
        return false;
    std::vector<DeclarationId> implementations;
    for (unsigned index = 0; index < storage.declarations.size(); ++index) {
      const auto &decl = storage.declarations[index];
      if (!types.charge(1, decl.span))
        return false;
      if (decl.id.index != index)
        return types.fail("source.scoped-witness",
                          "invalid declaration identity", decl.span);
      auto source = headers.sources.find(decl.id.index);
      const bool implements =
          source != headers.sources.end() &&
          source->second->kind == Declaration::Kind::Module &&
          source->second->definition.has_value();
      if (implements)
        implementations.push_back(decl.id);
      if ((!implements && (!decl.conformance.empty() || decl.implementation)) ||
          (implements &&
           (!decl.implementation || decl.kind != Declaration::Kind::Module)))
        return types.fail("source.scoped-witness", "invalid conformance owner",
                          decl.span);
    }
    if (implementations.empty())
      return true;
    if (!storage.declarationIndex)
      return types.fail("source.scoped-witness",
                        "missing conformance namespaces", {});
    if (auto error = chargeSemanticIndex(storage.declarations, work))
      return types.accept(std::move(error));
    CheckedStorage replay(storage.capture, storage.installation);
    replay.declarations = storage.declarations;
    replay.assets = storage.assets;
    replay.sources = storage.sources;
    replay.declarationIndex = storage.declarationIndex;
    // The replay reader indexes parameters at construction. Do not seed that
    // index with candidate atoms/slots before authored telescopes replace them.
    for (const auto &[index, source] : headers.sources) {
      auto &decl = replay.declarations[index];
      for (const auto &parameter : decl.parameters) {
        if (!types.charge(parameter.name.size() + parameter.atom.size() + 1,
                          source->span))
          return false;
        for (const auto &argument : parameter.arguments)
          if (!types.chargeType(argument, source->span))
            return false;
      }
      decl.parameters.clear();
    }
    Checker reader(replay, work, SourceAccess{{0}});
    // Register dependencies before reading any signature. Replaying only the
    // two selected members would trust mutable aliases and associated domains
    // on which both authored signatures depend.
    for (const auto &[index, source] : headers.sources)
      if (!reader.prepareSignatureReconstruction(DeclarationId{index}, *source))
        return types.accept(reader.types.takeError());
    // Match the producer's declaration order so an already completed earlier
    // alias does not become a new deep dependency chain in the witness.
    for (const auto &[index, source] : headers.sources) {
      (void)source;
      if (!reader.reconstructSignature(DeclarationId{index}))
        return types.accept(reader.types.takeError());
    }
    for (const auto &[index, source] : headers.sources)
      if (!reconstructInferredResult(types, storage, *source,
                                     replay.declarations[index]))
        return false;
    // Conformance is a proof query over reconstructed premises. In particular,
    // it has no inference hooks and cannot consult candidate alias, permission
    // or interface bounds to justify a candidate implementation requirement.
    if (auto error = chargeSemanticIndex(replay.declarations, work))
      return types.accept(std::move(error));
    Semantics premises(replay.declarations, replay.assets, work);
    std::set<uint32_t> reconstructed;
    std::function<bool(DeclarationId)> reconstruct = [&](DeclarationId id) {
      if (!reconstructed.insert(id.index).second)
        return true;
      auto source = headers.sources.find(id.index);
      if (source == headers.sources.end())
        return types.fail("source.scoped-witness", "missing authored contract",
                          {});
      const auto &actual = storage.declarations[id.index];
      auto canonical =
          storage.declarationIndex->canonical(actual.qualifiedName);
      if (!canonical || canonical->index != id.index)
        return types.fail("source.scoped-witness",
                          "authored contract identity differs", actual.span);
      auto parent = headers.parents.find(id.index);
      if (bool(actual.parent) != (parent != headers.parents.end()) ||
          (actual.parent && actual.parent->index != parent->second) ||
          actual.module.index >= storage.declarations.size())
        return types.fail("source.scoped-witness",
                          "authored contract owner differs", actual.span);
      auto owner = id.index;
      std::set<uint32_t> ancestors;
      while (headers.sources.at(owner)->kind != Declaration::Kind::Module) {
        if (!ancestors.insert(owner).second || !headers.parents.count(owner))
          return types.fail("source.scoped-witness",
                            "invalid authored module owner", actual.span);
        owner = headers.parents.at(owner);
      }
      if (actual.module.index != owner)
        return types.fail("source.scoped-witness",
                          "cached module owner differs", actual.span);
      if (actual.parent && !reconstruct(*actual.parent))
        return false;
      if (!reader.reconstructSignature(id)) {
        if (reader.types.diagnostic)
          return types.accept(reader.types.takeError());
        return types.fail("source.scoped-witness", "invalid authored contract",
                          actual.span);
      }
      if (!signatureAgrees(premises, actual, replay.declarations[id.index],
                           reader.permitsContractInference(id)))
        return types.accept(premises.takeError());
      return true;
    };
    for (auto id : implementations) {
      const auto &module = storage.declarations[id.index];
      const auto &source = *headers.sources.at(id.index);
      auto selection = storage.declarationIndex->lookup(
          SourceAccess{id}, source.definition->name,
          {[&] { return types.charge(1, source.definition->span); }, {}});
      const auto *reference = std::get_if<ResolvedReference>(&selection);
      auto contract =
          reference ? std::optional(reference->target) : std::nullopt;
      if (!contract || contract->index >= storage.declarations.size())
        return types.fail("source.scoped-witness", "missing authored interface",
                          module.span);
      auto writtenInterface = headers.sources.find(contract->index);
      if (writtenInterface == headers.sources.end() ||
          writtenInterface->second->kind != Declaration::Kind::Interface)
        return types.fail("source.scoped-witness", "invalid authored interface",
                          module.span);
      const auto &interface = storage.declarations[contract->index];
      if (interface.kind != Declaration::Kind::Interface ||
          module.implementation->domain != interface.qualifiedName ||
          !reconstruct(*contract) || !reconstruct(id))
        return types.diagnostic
                   ? false
                   : types.fail("source.scoped-witness",
                                "module interface differs", module.span);
      const auto &requiredSources = writtenInterface->second->members;
      if (module.conformance.size() != requiredSources.size() ||
          interface.members.size() != requiredSources.size())
        return types.fail("source.scoped-witness",
                          "conformance edge coverage differs", module.span);
      std::set<uint32_t> providedIds;
      const auto &writtenModule = replay.declarations[id.index];
      const auto &writtenContract = replay.declarations[contract->index];
      auto bindings = premises.substitution(
          writtenContract, writtenModule.implementation->arguments);
      Type self(Type::Kind::Module, writtenModule.qualifiedName);
      for (const auto &p : writtenModule.parameters)
        self.arguments.push_back(parameterType(p));
      bindings.emplace("self:" + interface.qualifiedName, std::move(self));
      for (unsigned i = 0; i < requiredSources.size(); ++i) {
        const auto &requiredSource = requiredSources[i];
        auto requiredId = storage.declarationIndex->canonical(
            interface.qualifiedName + "::" + requiredSource.name);
        auto providedId = storage.declarationIndex->canonical(
            module.qualifiedName + "::" + requiredSource.name);
        const auto &edge = module.conformance[i];
        if (!requiredId || !providedId ||
            edge.required.index != requiredId->index ||
            edge.provided.index != providedId->index ||
            interface.members[i].index != requiredId->index ||
            edge.provided.index >= storage.declarations.size() ||
            !providedIds.insert(edge.provided.index).second)
          return types.fail("source.scoped-witness",
                            "conformance edge differs from source",
                            module.span);
        const auto &required = storage.declarations[requiredId->index];
        const auto &provided = storage.declarations[providedId->index];
        auto ownSource = headers.sources.find(providedId->index);
        if (ownSource == headers.sources.end() ||
            ownSource->second->kind != requiredSource.kind ||
            headers.parents.find(providedId->index) == headers.parents.end() ||
            headers.parents.at(providedId->index) != id.index ||
            !required.parent || required.parent->index != contract->index ||
            !provided.parent || provided.parent->index != id.index ||
            provided.module.index != id.index ||
            required.name != requiredSource.name ||
            provided.name != requiredSource.name ||
            required.kind != requiredSource.kind ||
            provided.kind != requiredSource.kind ||
            llvm::count_if(module.members, [&](auto member) {
              return member.index == providedId->index;
            }) != 1)
          return types.fail("source.scoped-witness",
                            "conformance member owner or kind differs",
                            module.span);
        if (!reconstruct(*requiredId) || !reconstruct(*providedId))
          return false;
        if (!implementationAgrees(premises, writtenModule, writtenContract,
                                  replay.declarations[requiredId->index],
                                  provided, bindings))
          return types.accept(premises.takeError());
      }
    }
    return true;
  };
  if (verify())
    return llvm::Error::success();
  if (types.diagnostic && types.diagnostic->code != "source.limit" &&
      types.diagnostic->code != "source.cancelled")
    types.diagnostic->code = "source.scoped-witness";
  return types.diagnostic
             ? types.takeError()
             : failure("source.scoped-witness", "conformance contract differs");
}
} // namespace zkc::language::detail
