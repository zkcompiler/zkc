#include "Admission.h"
#include "zkc/Support/Refusal.h"
#include <algorithm>

using namespace llvm;
namespace zkc::mathematical {

Expected<uint32_t> AdmissionBuilder::instance(uint32_t index,
                                              ArrayRef<uint64_t> statics,
                                              ArrayRef<uint32_t> roleMap,
                                              ArrayRef<uint32_t> roots,
                                              unsigned depth) {
  if (auto failure =
          budget.consume(1 + statics.size() + roleMap.size() + roots.size()))
    return failure;
  if (depth > 256)
    return error("math-admission-limit");
  std::string key = std::to_string(index) + '|';
  for (auto value : statics)
    key += std::to_string(value) + ',';
  key += '|';
  for (auto value : roleMap)
    key += std::to_string(value) + ',';
  key += '|';
  for (auto value : roots)
    key += std::to_string(value) + ',';
  auto previous = instanceIds.find(key);
  if (previous != instanceIds.end())
    return previous->second;
  if (index >= source.module.definitions.size())
    return error("math-definition-reference");
  std::vector<NormalStatic> params;
  for (auto value : statics)
    params.push_back(NormalStatic::literal(value));
  auto formed = definition(index, params);
  if (!formed)
    return formed.takeError();
  if (roleMap.size() != formed->roleArity)
    return error("math-role-arity");
  if (roots.size() != formed->capabilities.size())
    return error("math-capability-arity");
  for (size_t i = 0; i < roots.size(); ++i) {
    if (roots[i] >= rootPermissions.size())
      return error("math-root-reference");
    const auto &root = rootPermissions[roots[i]];
    const auto &formal = formed->capabilities[i];
    if (!(root.signature == formal.signature))
      return error("math-root-signature");
    for (auto role : formal.roles) {
      if (auto failure = budget.consume())
        return failure;
      if (role >= roleMap.size() ||
          roleMap[role] >= source.module.roles.size() ||
          !std::binary_search(root.roles.begin(), root.roles.end(),
                              roleMap[role]))
        return error("math-root-permission");
    }
  }
  auto result = static_cast<uint32_t>(closedInstances.size());
  instanceIds.emplace(std::move(key), result);
  closedInstances.push_back({index,
                             statics.vec(),
                             roleMap.vec(),
                             roots.vec(),
                             std::move(*formed),
                             {}});
  // Deque storage keeps bodies stable during recursive discovery. Indexed
  // counts are never traversed: every stored body is inspected exactly once.
  if (auto failure =
          discover(result, closedInstances[result].typed.body, depth))
    return failure;
  return result;
}

Error AdmissionBuilder::discover(uint32_t caller, const TypedBody &body,
                                 unsigned depth) {
  for (const auto &step : body.steps) {
    if (auto failure = budget.consume())
      return failure;
    if (step.kind == TypedStep::Kind::Local) {
      if (!step.declaration)
        return error("math-internal-declaration");
      const auto &operation = source.module.operations[*step.declaration];
      for (const auto &pair : operation.distinct) {
        if (auto failure = budget.consume())
          return failure;
        if (pair.second >= step.capabilities.size())
          return error("math-distinct-contract");
        const auto &bindings = closedInstances[caller].roots;
        if (step.capabilities[pair.first] >= bindings.size() ||
            step.capabilities[pair.second] >= bindings.size())
          return error("math-capability-reference");
        if (bindings[step.capabilities[pair.first]] ==
            bindings[step.capabilities[pair.second]])
          return error("math-distinct-roots");
      }
    }
    if (step.kind == TypedStep::Kind::Invoke) {
      if (!step.declaration || !step.site)
        return error("math-internal-declaration");
      std::vector<uint64_t> statics;
      for (const auto &term : step.statics) {
        auto value = term.closed();
        if (!value)
          return value.takeError();
        statics.push_back(*value);
      }
      std::vector<uint32_t> roles, roots;
      const auto &parent = closedInstances[caller];
      for (auto role : step.roles) {
        if (role >= parent.roles.size())
          return error("math-role-binding");
        roles.push_back(parent.roles[role]);
      }
      for (auto capability : step.capabilities) {
        if (capability >= parent.roots.size())
          return error("math-capability-reference");
        roots.push_back(parent.roots[capability]);
      }
      auto callee =
          instance(*step.declaration, statics, roles, roots, depth + 1);
      if (!callee)
        return callee.takeError();
      closedInstances[caller].callees.emplace_back(*step.site, *callee);
    }
    if (step.kind == TypedStep::Kind::Repeat) {
      if (!step.body)
        return error("math-internal-body");
      if (auto failure = discover(caller, *step.body, depth))
        return failure;
    }
  }
  return Error::success();
}
} // namespace zkc::mathematical
