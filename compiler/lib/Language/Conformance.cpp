#include "Checker.h"
#include "zkc/Language/Builtins.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
bool Checker::conformance(DeclarationId id) {
  auto &component = output.declarations[id.index];
  auto &selected = *component.implementation;
  auto *interface = types.typeDeclaration(selected);
  auto bindings = types.substitution(*interface, selected.arguments);
  Type self(Type::Kind::Component, component.qualifiedName);
  for (auto &p : component.parameters)
    self.arguments.push_back(parameterType(p));
  bindings.emplace("self:" + interface->qualifiedName, self);
  if (interface->members.size() != component.members.size())
    return types.fail("source.conformance",
                      "component must implement every member exactly once",
                      component.span);
  for (auto requiredId : interface->members) {
    auto &required = output.declarations[requiredId.index];
    const Declaration *provided = nullptr;
    if (!types.charge(component.members.size(), required.span))
      return false;
    for (auto providedId : component.members)
      if (output.declarations[providedId.index].name == required.name)
        provided = &output.declarations[providedId.index];
    if (!provided || provided->kind != required.kind)
      return types.fail(
          "source.conformance",
          "component member missing or has a different callable mode",
          component.span);
    if (required.kind == Declaration::Kind::Associated) {
      auto sort = required.associatedSort;
      if (isDomainSort(sort) && (domainSort(provided->domain) != sort ||
                                 provided->associatedSort != sort))
        return types.fail("source.conformance",
                          "associated domain sort differs", provided->span);
      if (!provided->permissions.value_or(Permissions{})
               .includes(required.permissions.value_or(Permissions{})))
        return types.fail("source.conformance",
                          "associated type lacks promised permissions",
                          provided->span);
      if (isStaticOnly(provided->domain)) {
        if (!isDomainSort(sort))
          return types.fail(
              "source.conformance",
              "static domain cannot satisfy a runtime associated type",
              provided->span);
        continue;
      }
      auto caps =
          types.permissions(provided->domain, provided->span, &component);
      if (!caps)
        return false;
      if (!caps->includes(provided->permissions.value_or(Permissions{})))
        return types.fail("source.permission",
                          "associated permissions exceed representation",
                          provided->span);
    } else {
      if (required.inputs.size() != provided->inputs.size() ||
          required.outputs.size() != provided->outputs.size())
        return types.fail("source.conformance", "member arity differs",
                          provided->span);
      if (required.parameters.size() != interface->parameters.size() ||
          provided->parameters.size() != component.parameters.size())
        return types.fail("source.unsupported",
                          "member-level generic parameters need a separate "
                          "conformance contract",
                          provided->span);
      if (!chargeStaticSignature(component))
        return false;
      Declaration available{};
      available.span = component.span;
      available.parameters = component.parameters;
      available.bounds = component.bounds;
      available.permissionBounds = component.permissionBounds;
      available.capabilityBounds = component.capabilityBounds;
      for (const auto &bound : required.capabilityBounds) {
        CapabilityBound assumption{bound.predicate, {}, bound.span};
        for (const auto &argument : bound.arguments) {
          auto actual = types.substitute(argument, bindings, provided->span);
          if (!actual)
            return false;
          assumption.arguments.push_back(std::move(*actual));
        }
        if (llvm::none_of(assumption.arguments,
                          [&](const auto &t) { return types.symbolic(t); })) {
          if (!types.entails(nullptr, assumption, "source.conformance"))
            return false;
        } else
          available.capabilityBounds.push_back(std::move(assumption));
      }
      for (const auto &bound : provided->capabilityBounds)
        if (!types.entails(&available, bound, "source.conformance"))
          return false;
      for (const auto &parameter : required.parameters) {
        auto actual = bindings.find(parameter.atom);
        if (actual != bindings.end() &&
            !(parameter.permissions == Permissions{})) {
          if (!types.chargeType(actual->second, provided->span))
            return false;
          available.permissionBounds.push_back(
              {actual->second, parameter.permissions, parameter.span});
        }
      }
      for (const auto &bound : required.bounds) {
        Type lhs(Type::Kind::Natural), rhs(Type::Kind::Natural);
        lhs.dimension = bound.lhs;
        rhs.dimension = bound.rhs;
        auto l = types.substitute(lhs, bindings, provided->span);
        auto r = types.substitute(rhs, bindings, provided->span);
        if (!l || !r)
          return false;
        available.bounds.push_back({l->dimension, r->dimension, bound.span});
      }
      for (const auto &bound : required.permissionBounds) {
        auto type = types.substitute(bound.type, bindings, provided->span);
        if (!type)
          return false;
        available.permissionBounds.push_back(
            {*type, bound.permissions, bound.span});
      }
      for (const auto &bound : provided->permissionBounds) {
        Type requirement = bound.type;
        requirement.assumptions = {};
        auto resolved = types.substitute(requirement, {}, provided->span);
        if (!resolved)
          return false;
        auto caps = types.permissions(*resolved, provided->span, &available);
        if (!caps)
          return false;
        if (!caps->includes(bound.permissions))
          return types.fail("source.conformance",
                            "member adds an associated permission precondition",
                            provided->span);
      }
      for (const auto &bound : provided->bounds)
        if (!types.assumptions(available, bound, {}, provided->span))
          return false;
      for (unsigned i = 0; i < provided->parameters.size(); ++i) {
        if (isStaticOnly(parameterType(provided->parameters[i])))
          continue;
        auto allowed = types.permissions(parameterType(component.parameters[i]),
                                         provided->span, &available);
        if (!allowed)
          return false;
        if (!allowed->includes(provided->parameters[i].permissions))
          return types.fail("source.conformance",
                            "member adds a permission precondition",
                            provided->span);
      }
      for (bool input : {true, false}) {
        auto &a = input ? required.inputs : required.outputs;
        auto &b = input ? provided->inputs : provided->outputs;
        for (unsigned i = 0; i < a.size(); ++i) {
          auto expected = types.substitute(a[i].type, bindings, provided->span);
          if (!expected)
            return false;
          if (*expected != b[i].type)
            return types.fail("source.conformance", "member signature differs",
                              provided->span);
        }
      }
      auto allowance = required.effectAllowance.value_or(
          Effects{required.kind == Declaration::Kind::Local,
                  required.kind == Declaration::Kind::Local});
      auto &mutableProvided = output.declarations[provided->id.index];
      if (mutableProvided.effectAllowance) {
        auto p = *mutableProvided.effectAllowance;
        if ((p.mayStop && !allowance.mayStop) ||
            (p.opaque && !allowance.opaque))
          return types.fail("source.conformance",
                            "member effect allowance exceeds interface",
                            provided->span);
      } else
        mutableProvided.effectAllowance = allowance;
    }
  }
  return true;
}
} // namespace zkc::language::detail
