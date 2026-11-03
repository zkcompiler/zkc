#include "BindingWitness.h"
#include "BodyCheck.h"
#include <algorithm>
#include <cassert>
using namespace llvm;
namespace zkc::language::detail {
bool BodyChecker::product(ValueId id) const {
  const auto &value = body.values[id.index];
  return value.placement &&
         std::holds_alternative<ProductPlacement>(value.placement->value);
}
bool BodyChecker::matchPlacement(ValueId id, const ValuePlacement &expected,
                                 Span span) {
  const auto &value = body.values[id.index];
  if (const auto *data = std::get_if<DataPlacement>(&expected.value)) {
    if (isLogicalValue(value.type) || product(id))
      return fail("source.placement",
                  "logical value cannot supply ordinary data", span);
    auto actual = components(id);
    if (!active(data->roles, span) || !demand(id, data->roles, span))
      return false;
    return !actual.owners.empty() || actual.roles == data->roles ||
           checker.types.requireUsage(
               value.type, Usage::Drop, span, &decl, "source.permission",
               "placement cannot discard components without Drop");
  }
  std::optional<ValuePlacement> actual = value.placement;
  if (!actual && isOracleHandle(value.type) && value.oracleHolder) {
    auto receivers = components(id).roles;
    receivers.erase(
        std::remove(receivers.begin(), receivers.end(), *value.oracleHolder),
        receivers.end());
    actual = OraclePlacement{*value.oracleHolder, std::move(receivers)};
  }
  return (actual && *actual == expected &&
          active(placementRoles(expected), span)) ||
         fail("source.placement", "exact placed identity differs", span);
}

std::optional<ValuePlacement>
BodyChecker::inferRecordPlacement(const Type &type, ArrayRef<TypeField> fields,
                                  ArrayRef<ValueId> values, Span span) {
  const auto *definition = checker.types.typeDeclaration(type);
  if (!definition || definition->roles.empty()) {
    fail("source.placement", "record has no role telescope", span);
    return {};
  }
  const unsigned count = definition->roles.size();
  if (!checker.types.charge(uint64_t(count) * (decl.roles.size() + 1), span))
    return {};
  std::vector<std::vector<unsigned>> domains(count, allRoles());
  auto narrow = [&](unsigned formal, ArrayRef<unsigned> allowed) {
    if (!checker.types.charge(domains[formal].size() + allowed.size() + 1,
                              span))
      return false;
    std::vector<unsigned> intersection;
    std::set_intersection(domains[formal].begin(), domains[formal].end(),
                          allowed.begin(), allowed.end(),
                          std::back_inserter(intersection));
    domains[formal] = std::move(intersection);
    return true;
  };
  std::function<bool(const Type &, const ValuePlacement &,
                     const ValuePlacement &, unsigned)>
      equations = [&](const Type &fieldType, const ValuePlacement &formula,
                      const ValuePlacement &actual, unsigned depth) {
        if (depth > checker.work.limits.typeDepth)
          return fail("source.limit",
                      "record placement inference depth exceeded", span);
        if (!checker.types.charge(1, span))
          return false;
        if (const auto *data = std::get_if<DataPlacement>(&formula.value)) {
          const auto *available = std::get_if<DataPlacement>(&actual.value);
          if (!available)
            return fail("source.placement", "ordinary field requires data",
                        span);
          for (auto formal : data->roles)
            if (!narrow(formal, available->roles))
              return false;
        } else if (const auto *oracle =
                       std::get_if<OraclePlacement>(&formula.value)) {
          const auto *family = std::get_if<OraclePlacement>(&actual.value);
          if (!family)
            return fail("source.placement",
                        "oracle field has no concrete family", span);
          if (!narrow(oracle->holder, {family->holder}))
            return false;
          if (family->receivers.size() != oracle->receivers.size())
            return fail("source.placement",
                        "oracle field receiver arity differs", span);
          // Receivers are a canonical set, not an ordered role substitution.
          for (auto formal : oracle->receivers)
            if (!narrow(formal, family->receivers))
              return false;
        } else {
          const auto &nested = std::get<ProductPlacement>(formula.value);
          const auto *product = std::get_if<ProductPlacement>(&actual.value);
          if (!product || product->instance != nested.instance)
            return fail("source.placement", "nested field has no exact schema",
                        span);
          if (fieldType.kind == Type::Kind::Tuple ||
              fieldType.kind == Type::Kind::Array) {
            if (nested.fields.size() != fieldType.arguments.size() ||
                product->fields.size() != nested.fields.size())
              return fail("source.placement",
                          "structural field schema arity differs", span);
            // Structural arguments summarize participation. Equations come from
            // the child schemas, including an array's element at extent zero.
            for (unsigned i = 0; i < nested.fields.size(); ++i)
              if (!equations(fieldType.arguments[i], nested.fields[i],
                             product->fields[i], depth + 1))
                return false;
          } else {
            if (product->arguments.size() != nested.arguments.size())
              return fail("source.placement",
                          "nominal role telescope arity differs", span);
            for (unsigned i = 0; i < nested.arguments.size(); ++i)
              if (!narrow(nested.arguments[i], {product->arguments[i]}))
                return false;
          }
        }
        return true;
      };
  for (unsigned i = 0; i < fields.size(); ++i) {
    if (!checker.types.charge(1, span) || !fields[i].placement)
      return {};
    const auto &value = body.values[values[i].index];
    auto roles = components(values[i]).roles;
    ValuePlacement fallback = DataPlacement{roles};
    if (!value.placement && value.oracleHolder) {
      roles.erase(std::remove(roles.begin(), roles.end(), *value.oracleHolder),
                  roles.end());
      fallback = OraclePlacement{*value.oracleHolder, std::move(roles)};
    }
    if (!equations(fields[i].type, *fields[i].placement,
                   value.placement ? *value.placement : fallback, 1))
      return {};
  }
  std::vector<unsigned> mapping(count, decl.roles.size());
  std::set<unsigned> used;
  std::optional<ValuePlacement> solution;
  unsigned solutions = 0;
  std::function<bool(unsigned)> search = [&](unsigned assigned) {
    if (!checker.types.charge(1, span))
      return false;
    if (solutions > 1)
      return true;
    if (assigned == count) {
      auto candidate = checker.types.placement(
          type, ProductPlacement{typeIdentity(type), mapping, {}},
          decl.roles.size(), span);
      if (!candidate)
        return false;
      const auto &product = std::get<ProductPlacement>(candidate->value);
      for (unsigned i = 0; i < values.size(); ++i) {
        const auto &actual = body.values[values[i].index];
        if (const auto *data =
                std::get_if<DataPlacement>(&product.fields[i].value)) {
          auto available = components(values[i]).roles;
          if (!std::includes(available.begin(), available.end(),
                             data->roles.begin(), data->roles.end()))
            return true;
        } else if (actual.placement) {
          if (*actual.placement != product.fields[i])
            return true;
        } else if (const auto *oracle =
                       std::get_if<OraclePlacement>(&product.fields[i].value)) {
          if (actual.oracleHolder != oracle->holder ||
              components(values[i]).roles != placementRoles(product.fields[i]))
            return true;
        } else
          return true;
      }
      ++solutions;
      solution = std::move(candidate);
      return true;
    }
    unsigned next = count;
    for (unsigned i = 0; i < count; ++i)
      if (mapping[i] == decl.roles.size() &&
          (next == count || domains[i].size() < domains[next].size()))
        next = i;
    for (auto role : domains[next]) {
      if (!checker.types.charge(1, span))
        return false;
      if (used.count(role))
        continue;
      mapping[next] = role;
      used.insert(role);
      if (!search(assigned + 1))
        return false;
      used.erase(role);
      mapping[next] = decl.roles.size();
      if (solutions > 1)
        break;
    }
    return true;
  };
  if (!search(0))
    return {};
  if (solutions != 1) {
    fail("source.placement-inference",
         solutions ? "record role application is ambiguous; supply an expected "
                     "placement"
                   : "record fields have no injective role application",
         span);
    return {};
  }
  return solution;
}
BodyChecker::StatementPlacement::StatementPlacement(BodyChecker &checker)
    : checker(checker), outer(checker.placement) {
  if (checker.protocol()) {
    state.emplace(checker.checker.types, checker.decl, checker.allRoles(),
                  outer);
    checker.placement = &*state;
  }
}
BodyChecker::StatementPlacement::~StatementPlacement() {
  checker.placement = outer;
}
bool BodyChecker::StatementPlacement::commit() {
  if (state && !checker.settle(*state))
    return false;
  checker.placement = outer;
  return true;
}
Components BodyChecker::components(ValueId value) const {
  if (placement) {
    auto found = placement->values.find(value.index);
    if (found != placement->values.end())
      return found->second;
#ifndef NDEBUG
    for (auto *parent = placement->enclosing; parent;
         parent = parent->enclosing) {
      auto valueInParent = parent->values.find(value.index);
      assert((valueInParent == parent->values.end() ||
              valueInParent->second.owners.empty()) &&
             "unsettled value crossed a statement boundary");
    }
#endif
  }
  return Components(body.values[value.index].components);
}
bool BodyChecker::demand(ValueId value, ArrayRef<unsigned> roles, Span span) {
  if (product(value) && !roles.empty())
    return fail("source.placement",
                "a product participation summary grants no data access", span);
  if (placement)
    return placement->demand(components(value), roles, span);
  const auto &available = body.values[value.index].components;
  return std::includes(available.begin(), available.end(), roles.begin(),
                       roles.end()) ||
         fail("source.roles",
              "expression is unavailable at the required participant", span);
}
bool BodyChecker::settle(Placement &plan) {
  if (!plan.solve())
    return false;
  // These values and actions are an unpublished statement plan. Only concrete
  // component sets and owners are retained by the checked body.
  for (const auto &[id, formula] : plan.values) {
    auto &value = body.values[id];
    value.components = plan.resolve(formula);
    if (!isLogicalValue(value.type) && !product(ValueId{id}))
      value.placement = DataPlacement{value.components};
    if (value.components.size() > 1 && !isLogicalValue(value.type) &&
        !product(ValueId{id})) {
      if (!checker.types.admit(value.type, Boundary::Participants, value.span,
                               &decl))
        return false;
    }
  }
  for (auto [index, variable] : plan.calls) {
    auto &operation = body.operations[index];
    auto &call = std::get<HelperCall>(operation.action);
    call.owner = plan.selected(variable);
    for (auto arg : call.operands)
      if (body.values[arg.index].components.size() > 1) {
        if (!checker.types.requireUsage(
                body.values[arg.index].type, Usage::Copy, operation.span, &decl,
                "source.permission",
                "owned call cannot duplicate or discard restricted components"))
          return false;
      }
  }
  for (auto index : plan.oracleInstantiations)
    if (!checkCallAction(checker.types, checker.output.declarations, body,
                         body.operations[index]))
      return false;
  for (auto [index, variable] : plan.oracleQueries)
    std::get<OracleQuery>(body.operations[index].action).owner =
        plan.selected(variable);
  for (auto index : plan.applications) {
    const auto &operation = body.operations[index];
    if (!checkCallAction(checker.types, checker.output.declarations, body,
                         operation, checker.output.declarationIndex.get()))
      return false;
    const auto &application = std::get<ProtocolApplication>(operation.action);
    const auto &callee = checker.output.declarations[application.callee.index];
    for (unsigned i = 0; i < application.operands.size(); ++i) {
      const auto &value = body.values[application.operands[i].index];
      std::vector<unsigned> roles;
      for (auto role : callee.inputs[i].roles)
        roles.push_back(application.roles[role]);
      llvm::sort(roles);
      if (value.components != roles) {
        if (!checker.types.requireUsage(
                value.type, Usage::Drop, operation.span, &decl,
                "source.permission",
                "application cannot discard a component without Drop"))
          return false;
      }
    }
  }
  return true;
}
} // namespace zkc::language::detail
