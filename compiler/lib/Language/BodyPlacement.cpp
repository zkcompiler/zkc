#include "BodyCheck.h"
#include <algorithm>
#include <cassert>
using namespace llvm;
namespace zkc::language::detail {
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
    if (value.components.size() > 1) {
      auto caps = checker.types.permissions(value.type, value.span, &decl);
      if (!caps || !caps->share)
        return checker.types.diagnostic
                   ? false
                   : fail("source.permission",
                          "multiple participant components require Share",
                          value.span);
    }
  }
  for (auto [index, variable] : plan.calls) {
    auto &operation = body.operations[index];
    auto &call = std::get<HelperCall>(operation.action);
    call.owner = plan.selected(variable);
    for (auto arg : call.operands)
      if (body.values[arg.index].components.size() > 1) {
        auto caps = checker.types.permissions(body.values[arg.index].type,
                                              operation.span, &decl);
        if (!caps || !caps->copy || !caps->drop)
          return checker.types.diagnostic
                     ? false
                     : fail("source.permission",
                            "owned call cannot duplicate or discard restricted "
                            "components",
                            operation.span);
      }
  }
  for (auto index : plan.applications) {
    const auto &operation = body.operations[index];
    const auto &application = std::get<ProtocolApplication>(operation.action);
    const auto &callee = checker.output.declarations[application.callee.index];
    for (unsigned i = 0; i < application.operands.size(); ++i) {
      const auto &value = body.values[application.operands[i].index];
      std::vector<unsigned> roles;
      for (auto role : callee.inputs[i].roles)
        roles.push_back(application.roles[role]);
      llvm::sort(roles);
      if (value.components != roles) {
        auto caps =
            checker.types.permissions(value.type, operation.span, &decl);
        if (!caps || !caps->drop)
          return checker.types.diagnostic ? false
                                          : fail("source.permission",
                                                 "application cannot discard a "
                                                 "component without Drop",
                                                 operation.span);
      }
    }
  }
  return true;
}
} // namespace zkc::language::detail
