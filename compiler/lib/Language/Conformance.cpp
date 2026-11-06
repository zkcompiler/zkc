#include "Conformance.h"
#include "Checker.h"
#include "Effects.h"
#include "zkc/Language/Builtins.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
bool memberInputs(Semantics &types, const Declaration &required,
                  const Declaration &provided, const Substitution &bindings,
                  StringRef diagnostic) {
  auto refuse = [&] {
    return types.fail(diagnostic,
                      "member input or result contract differs from interface",
                      provided.span);
  };
  if (!types.charge(required.inputOrder.size() +
                        required.descriptorInputs.size() +
                        required.scopedInputs.size() + required.inputs.size() +
                        required.outputs.size() + required.services.size() + 1,
                    provided.span))
    return false;
  if (required.kind != provided.kind ||
      required.roles.size() != provided.roles.size() ||
      required.inputs.size() != provided.inputs.size() ||
      required.outputs.size() != provided.outputs.size() ||
      required.services.size() != provided.services.size() ||
      bool(required.descriptorResult) != bool(provided.descriptorResult) ||
      required.inputOrder.size() != provided.inputOrder.size() ||
      required.descriptorInputs.size() != provided.descriptorInputs.size() ||
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
  auto sameContract = [&](const DescriptorContract &expected,
                          const DescriptorContract &actual) {
    if (!types.chargeContract(actual, provided.span))
      return false;
    auto resolved = types.substitute(expected, bindings, provided.span);
    return resolved && (*resolved == actual || refuse());
  };
  for (bool input : {true, false}) {
    const auto &expected = input ? required.inputs : required.outputs;
    const auto &actual = input ? provided.inputs : provided.outputs;
    for (unsigned i = 0; i < expected.size(); ++i) {
      const auto &a = expected[i], &b = actual[i];
      auto placed =
          types.substitutePlaced({a.type, a.placement}, bindings,
                                 provided.roles.size(), provided.span);
      if (!placed)
        return false;
      if (placed->type != b.type || placed->placement != b.placement ||
          a.roles != b.roles || bool(a.oracle) != bool(b.oracle))
        return refuse();
      if (a.oracle) {
        if (a.oracle->holder != b.oracle->holder ||
            bool(a.oracle->maximumRows) != bool(b.oracle->maximumRows))
          return refuse();
        if (a.oracle->maximumRows &&
            !sameType(*a.oracle->maximumRows, *b.oracle->maximumRows))
          return false;
      }
    }
  }
  for (unsigned i = 0; i < required.services.size(); ++i) {
    const auto &a = required.services[i], &b = provided.services[i];
    if (a.owner != b.owner ||
        a.constructor.target.index != b.constructor.target.index ||
        a.constructor.category != b.constructor.category)
      return refuse();
    if (!sameType(a.field, b.field))
      return false;
  }
  if (required.descriptorResult &&
      !sameContract(*required.descriptorResult, *provided.descriptorResult))
    return false;
  for (unsigned i = 0; i < required.descriptorInputs.size(); ++i)
    if (!sameContract(required.descriptorInputs[i].contract,
                      provided.descriptorInputs[i].contract))
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
namespace {
// Permission caches in a candidate obligation are not premises, including
// caches nested in a product. The caller charges and bounds the tree first.
void clearPermissionAssumptions(Type &type) {
  type.assumptions = {};
  for (auto &argument : type.arguments)
    clearPermissionAssumptions(argument);
}
} // namespace
bool memberContract(Semantics &types, const Declaration &module,
                    const Declaration &interface, const Declaration &required,
                    const Declaration &provided, Substitution bindings,
                    StringRef diagnostic) {
  auto refuse = [&](StringRef message) {
    return types.fail(diagnostic, message, provided.span);
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
  const auto requiredOwner = interface.parameters.size();
  const auto providedOwner = module.parameters.size();
  if (required.parameters.size() < requiredOwner ||
      provided.parameters.size() < providedOwner ||
      required.parameters.size() - requiredOwner !=
          provided.parameters.size() - providedOwner ||
      required.inputs.size() != provided.inputs.size() ||
      required.outputs.size() != provided.outputs.size() ||
      bool(required.descriptorResult) != bool(provided.descriptorResult))
    return refuse("implementation signature arity differs");
  if (!types.charge(required.parameters.size() + provided.parameters.size() + 1,
                    provided.span))
    return false;
  // Declaration-qualified atoms, rather than written names, make this a
  // capture-avoiding positional renaming. Earlier binders are in scope in a
  // later module constraint. The implementation's permissions are goals below.
  for (unsigned i = 0; i < required.parameters.size() - requiredOwner; ++i) {
    const auto &a = required.parameters[requiredOwner + i];
    const auto &b = provided.parameters[providedOwner + i];
    if (!types.charge(a.atom.size() + b.atom.size() + a.arguments.size() + 1,
                      provided.span))
      return false;
    if (a.sort != b.sort || a.domainSort != b.domainSort ||
        bool(a.interface) != bool(b.interface) ||
        (a.interface && a.interface->index != b.interface->index) ||
        a.arguments.size() != b.arguments.size())
      return refuse("implementation member binder differs");
    for (unsigned j = 0; j < a.arguments.size(); ++j) {
      if (!types.chargeType(b.arguments[j], provided.span))
        return false;
      auto expected = types.substitute(a.arguments[j], bindings, provided.span);
      if (!expected)
        return false;
      if (*expected != b.arguments[j])
        return refuse("implementation member module constraint differs");
    }
    auto rigid = parameterType(b);
    if (!types.chargeType(rigid, provided.span))
      return false;
    clearPermissionAssumptions(rigid);
    bindings.emplace(a.atom, std::move(rigid));
  }
  if (!memberInputs(types, required, provided, bindings, diagnostic))
    return false;
  for (const auto &condition : provided.dataPreconditions) {
    if (!types.charge(required.dataPreconditions.size() + 1, provided.span))
      return false;
    if (!llvm::is_contained(required.dataPreconditions, condition))
      return refuse("implementation strengthens data preconditions");
  }
  // A deferred native boundary is still a caller requirement. A selected body
  // cannot hide construction/codec authority behind an abstract member whose
  // contract permits values that lack it. These are derived obligations, not
  // new usage permissions or an invitation to grant authority with `where`.
  std::set<std::pair<Boundary, std::string>> admissions;
  for (const auto *owner : {&module, &required}) {
    for (const auto &obligation : owner->admissions) {
      auto actual = types.substitute(
          obligation.type, owner == &required ? bindings : Substitution{},
          provided.span);
      if (!actual || !types.chargeType(*actual, provided.span))
        return false;
      clearPermissionAssumptions(*actual);
      if (!types.chargeIdentity(*actual, provided.span))
        return false;
      admissions.emplace(obligation.boundary, typeIdentity(*actual));
    }
  }
  for (const auto &obligation : provided.admissions) {
    if (!types.chargeType(obligation.type, provided.span) ||
        !types.charge(1, provided.span))
      return false;
    Type requirement = obligation.type;
    clearPermissionAssumptions(requirement);
    auto admitted =
        types.admission(requirement, obligation.boundary, provided.span);
    if (!admitted)
      return false;
    if (*admitted == Semantics::Admission::Accepted)
      continue;
    if (*admitted == Semantics::Admission::Rejected)
      return refuse(
          "implementation strengthens boundary admission requirements");
    if (!types.chargeIdentity(requirement, provided.span))
      return false;
    if (!admissions.count({obligation.boundary, typeIdentity(requirement)}))
      return refuse(
          "implementation strengthens boundary admission requirements");
  }
  Declaration available{};
  available.span = provided.span;
  available.parameters = module.parameters;
  for (unsigned i = providedOwner; i < provided.parameters.size(); ++i) {
    auto rigid = provided.parameters[i];
    rigid.permissions = {};
    available.parameters.push_back(std::move(rigid));
  }
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
    else if (!types.entails(nullptr, assumption, diagnostic))
      return false;
  }
  for (const auto &bound : provided.capabilityBounds)
    if (!types.entails(&available, bound, diagnostic))
      return false;
  for (const auto &bound : provided.bounds)
    if (!(provided.kind == Declaration::Kind::View && provided.descriptorResult
              ? types.structuralAssumptions(available, bound, {}, provided.span,
                                            diagnostic)
              : types.assumptions(available, bound, {}, provided.span)))
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
    auto rigid = parameterType(provided.parameters[i]);
    if (!types.chargeType(rigid, provided.span))
      return false;
    clearPermissionAssumptions(rigid);
    auto caps = types.permissions(rigid, provided.span, &available);
    if (!caps || (!caps->includes(provided.parameters[i].permissions) &&
                  !refuse("implementation strengthens parameter permissions")))
      return false;
  }
  if (required.kind == Declaration::Kind::View && required.descriptorResult)
    return bool(provided.descriptorDefinition) ||
           refuse("implementation domain recipe missing");
  if (!provided.body || required.completes != provided.completes)
    return refuse("implementation outcome contract differs");
  if (!effectsWithin(types, provided.body->effects,
                     required.effectAllowance.value_or(EffectSummary{}),
                     provided.span))
    return types.fail(
        diagnostic == "source.conformance" ? "source.effect" : diagnostic,
        "body exceeds its interface effect contract", provided.span);
  return true;
}
bool Checker::conformance(DeclarationId id) {
  auto &module = output.declarations[id.index];
  auto &selected = *module.implementation;
  auto *interface = types.typeDeclaration(selected);
  auto bindings = types.substitution(*interface, selected.arguments);
  Type self(Type::Kind::Module, module.qualifiedName);
  for (auto &p : module.parameters)
    self.arguments.push_back(parameterType(p));
  bindings.emplace("self:" + interface->qualifiedName, self);
  if (module.conformance.size() != interface->members.size())
    return types.fail("source.conformance", "module member edges incomplete",
                      module.span);
  for (const auto &edge : module.conformance) {
    auto &required = output.declarations[edge.required.index];
    const auto *provided = &output.declarations[edge.provided.index];
    if (required.kind != Declaration::Kind::Associated &&
        !body(provided->id, 1))
      return false;
    if (!chargeStaticSignature(module) ||
        !memberContract(types, module, *interface, required, *provided,
                        bindings, "source.conformance"))
      return false;
  }
  return true;
}
} // namespace zkc::language::detail
