#include "Checker.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
bool Checker::conformance(DeclarationId id) {
  auto &component = output.declarations[id.index];
  auto &selected = *component.implementation;
  auto *interface = typeDeclaration(selected);
  auto bindings = substitution(*interface, selected.arguments);
  Type self(Type::Kind::Component, component.qualifiedName);
  for (auto &p : component.parameters)
    self.arguments.push_back(parameterType(p));
  bindings.emplace("self:" + interface->qualifiedName, self);
  if (interface->members.size() != component.members.size())
    return fail("source.conformance",
                "component must implement every member exactly once",
                component.span);
  for (auto requiredId : interface->members) {
    auto &required = output.declarations[requiredId.index];
    const Declaration *provided = nullptr;
    for (auto providedId : component.members)
      if (output.declarations[providedId.index].name == required.name)
        provided = &output.declarations[providedId.index];
    if (!provided || provided->kind != required.kind)
      return fail("source.conformance",
                  "component member missing or has a different callable mode",
                  component.span);
    if (required.kind == Declaration::Kind::Associated) {
      auto sort = required.associatedSort;
      if ((sort == "Field" && provided->domain.kind != Type::Kind::Field) ||
          (sort == "Group" && provided->domain.kind != Type::Kind::Group) ||
          ((sort == "Field" || sort == "Group") &&
           provided->associatedSort != sort))
        return fail("source.conformance", "associated domain sort differs",
                    provided->span);
      if (!provided->permissions.value_or(Permissions{})
               .includes(required.permissions.value_or(Permissions{})))
        return fail("source.conformance",
                    "associated type lacks promised permissions",
                    provided->span);
      auto caps = permissions(provided->domain, provided->span, &component);
      if (!caps)
        return false;
      if (!caps->includes(provided->permissions.value_or(Permissions{})))
        return fail("source.permission",
                    "associated permissions exceed representation",
                    provided->span);
    } else {
      if (required.inputs.size() != provided->inputs.size() ||
          required.outputs.size() != provided->outputs.size())
        return fail("source.conformance", "member arity differs",
                    provided->span);
      if (required.parameters.size() != interface->parameters.size() ||
          provided->parameters.size() != component.parameters.size())
        return fail("source.unsupported",
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
      for (const auto &parameter : required.parameters) {
        auto actual = bindings.find(parameter.atom);
        if (actual != bindings.end() &&
            !(parameter.permissions == Permissions{})) {
          if (!chargeType(actual->second, provided->span))
            return false;
          available.permissionBounds.push_back(
              {actual->second, parameter.permissions, parameter.span});
        }
      }
      for (const auto &bound : required.bounds) {
        Type lhs(Type::Kind::Natural), rhs(Type::Kind::Natural);
        lhs.dimension = bound.lhs;
        rhs.dimension = bound.rhs;
        auto l = substitute(lhs, bindings, provided->span);
        auto r = substitute(rhs, bindings, provided->span);
        if (!l || !r)
          return false;
        available.bounds.push_back({l->dimension, r->dimension, bound.span});
      }
      for (const auto &bound : required.permissionBounds) {
        auto type = substitute(bound.type, bindings, provided->span);
        if (!type)
          return false;
        available.permissionBounds.push_back(
            {*type, bound.permissions, bound.span});
      }
      for (const auto &bound : provided->permissionBounds) {
        Type requirement = bound.type;
        requirement.assumptions = {};
        auto resolved = substitute(requirement, {}, provided->span);
        if (!resolved)
          return false;
        auto caps = permissions(*resolved, provided->span, &available);
        if (!caps)
          return false;
        if (!caps->includes(bound.permissions))
          return fail("source.conformance",
                      "member adds an associated permission precondition",
                      provided->span);
      }
      for (const auto &bound : provided->bounds)
        if (!assumptions(available, bound, {}, provided->span))
          return false;
      for (unsigned i = 0; i < provided->parameters.size(); ++i) {
        if (provided->parameters[i].sort == Parameter::Sort::Natural ||
            provided->parameters[i].sort == Parameter::Sort::Component)
          continue;
        auto allowed = permissions(parameterType(component.parameters[i]),
                                   provided->span, &available);
        if (!allowed)
          return false;
        if (!allowed->includes(provided->parameters[i].permissions))
          return fail("source.conformance",
                      "member adds a permission precondition", provided->span);
      }
      for (bool input : {true, false}) {
        auto &a = input ? required.inputs : required.outputs;
        auto &b = input ? provided->inputs : provided->outputs;
        for (unsigned i = 0; i < a.size(); ++i) {
          auto expected = substitute(a[i].type, bindings, provided->span);
          if (!expected)
            return false;
          if (*expected != b[i].type)
            return fail("source.conformance", "member signature differs",
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
          return fail("source.conformance",
                      "member effect allowance exceeds interface",
                      provided->span);
      } else
        mutableProvided.effectAllowance = allowance;
    }
  }
  return true;
}
} // namespace zkc::language::detail
