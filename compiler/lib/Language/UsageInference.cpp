#include "Checker.h"
#include "llvm/ADT/ScopeExit.h"
using namespace llvm;
namespace zkc::language::detail {
namespace {
bool appendRequirements(Semantics &types, const Declaration &decl,
                        std::vector<PermissionBound> &inferred,
                        const Type &type, Usage usage, Span span,
                        StringRef code, StringRef message) {
  auto leaves = types.usageRequirements(type, usage, span, decl, code, message);
  if (!leaves)
    return false;
  for (auto &leaf : *leaves) {
    auto found = llvm::find_if(
        inferred, [&](const auto &bound) { return bound.type == leaf; });
    if (found == inferred.end()) {
      inferred.push_back({std::move(leaf), {}, span, true});
      found = std::prev(inferred.end());
    }
    found->permissions.drop = true;
    found->permissions.copy |= usage == Usage::Copy;
  }
  return true;
}
} // namespace
bool Checker::collectUsage(const Declaration &scope, const Type &type,
                           Usage usage, Span span, StringRef code,
                           StringRef message) {
  if (!inferredContracts.count(&scope) || !types.chargeType(type, span))
    return false;
  if (auto *plan = bodyPlan(scope.id)) {
    plan->demands.push_back({type, usage, span, code.str(), message.str()});
    return true;
  }
  // Signatures and static definitions collect direct requirements without
  // a use plan. Completed definitions leave inferredContracts, like bodies.
  if (signatureState[scope.id.index] != 1 &&
      scope.kind != Declaration::Kind::Construction &&
      scope.kind != Declaration::Kind::DomainFunction)
    return false;
  auto &decl = output.declarations[scope.id.index];
  return appendRequirements(types, decl, decl.permissionBounds, type, usage,
                            span, code, message);
}
bool Checker::inferUsage(Declaration &decl, Body::Mode mode, unsigned depth) {
  BodyPlan plan(types, decl);
  Body scratch;
  scratch.mode = mode;
  bodyPlans.emplace(decl.id.index, &plan);
  {
    auto outputs = decl.outputs;
    scope_exit restore([&] {
      bodyPlans.erase(decl.id.index);
      decl.outputs = std::move(outputs);
    });
    if (!checkBody(decl, scratch, depth))
      return false;
  }
  // Scratch witnesses belong to this plan. Callees completed during collection
  // keep their own published witnesses; no global vector is rolled back.
  std::vector<PermissionBound> inferred;
  auto require = [&](const Type &type, Usage usage, Span span, StringRef code,
                     StringRef message) {
    return appendRequirements(types, decl, inferred, type, usage, span, code,
                              message);
  };
  for (const auto &demand : plan.demands)
    if (!require(demand.type, demand.usage, demand.span, demand.code,
                 demand.message))
      return false;
  if (!plan.usage.solve(require))
    return false;
  for (auto &bound : inferred) {
    auto found = decl.permissionBounds.end();
    for (auto at = decl.permissionBounds.begin();
         at != decl.permissionBounds.end(); ++at) {
      if (!types.chargeType(at->type, bound.span))
        return false;
      if (at->inferred && at->type == bound.type) {
        found = at;
        break;
      }
    }
    if (found == decl.permissionBounds.end())
      decl.permissionBounds.push_back(std::move(bound));
    else if (bound.permissions.copy && !found->permissions.copy)
      *found = std::move(bound);
  }
  return true;
}
} // namespace zkc::language::detail
