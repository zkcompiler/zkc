#include "Demand.h"
#include "zkc/Support/Refusal.h"
#include <algorithm>

using namespace llvm;
namespace zkc::mathematical {
SourceAddress bodyAddress(const ClosedInstance &instance, BindingId binding) {
  return {instance.definition, {}, binding.ordinal};
}
SourceAddress regionAddress(const ClosedInstance &instance, uint32_t step,
                            BindingId binding) {
  return {instance.definition, {step, 0}, binding.ordinal};
}
namespace {
struct Value {
  Port port;
  std::vector<SourceAddress> dependencies;
  // Only the sender's message component aliases the sent operand. The
  // receiver gets an arbitrary value of the admitted wire type.
  std::optional<uint32_t> dependencyRole;
};
} // namespace

Expected<Demand> computeDemand(const Subject &subject,
                               AdmissionBudget &budget) {
  if (subject.instances().size() != 1)
    return error("math-placement-instance-subset");
  if (subject.source().module.definitions.size() != 1)
    return error("math-placement-definition-subset");
  const auto &instance = subject.instances()[0];
  const auto &body = instance.typed.body;
  if (!subject.source().module.relations.empty() ||
      !instance.typed.relations.empty())
    return error("math-placement-relation-subset");
  // Every root is retained, including unused roots. This bounded profile has
  // no second instance whose roles could own otherwise unbound module roots.
  if (instance.roles.size() != subject.source().module.roles.size())
    return error("math-placement-role-subset");
  std::map<SourceAddress, Value> values;
  std::vector<ComponentKey> pending;
  auto seed = [&](SourceAddress address, uint32_t localRole) -> Error {
    if (auto failure = budget.consume())
      return failure;
    pending.push_back({std::move(address), instance.roles.at(localRole)});
    return Error::success();
  };
  for (size_t i = 0; i < body.parameters.size(); ++i) {
    auto address = bodyAddress(instance, body.parameterBindings[i]);
    values.emplace(address, Value{body.parameters[i], {}, {}});
    for (auto role : body.parameters[i].roles)
      if (auto failure = seed(address, role))
        return failure;
  }
  for (uint32_t i = 0; i < body.steps.size(); ++i) {
    if (auto failure = budget.consume())
      return failure;
    const auto &step = body.steps[i];
    if (step.kind == TypedStep::Kind::Pure) {
      const auto &region = *step.region;
      for (size_t j = 0; j < region.parameters.size(); ++j) {
        if (auto failure = budget.consume())
          return failure;
        values.emplace(
            regionAddress(instance, i, region.parameterBindings[j]),
            Value{region.parameters[j],
                  {bodyAddress(instance, region.captures[j].binding)},
                  {}});
      }
      for (const auto &node : region.nodes) {
        if (auto failure = budget.consume(1 + node.inputs.size()))
          return failure;
        if (node.kind != TypedNode::Kind::Operation)
          return error("math-placement-node-subset");
        if (!node.statics.empty() || !node.attributes.getAsObject() ||
            !node.attributes.getAsObject()->empty())
          return error("math-placement-operation-subset");
        std::vector<SourceAddress> dependencies;
        for (const auto &input : node.inputs)
          dependencies.push_back(regionAddress(instance, i, input.binding));
        values.emplace(regionAddress(instance, i, node.outputBindings[0]),
                       Value{node.outputs[0], std::move(dependencies), {}});
      }
      for (size_t j = 0; j < step.outputs.size(); ++j) {
        if (auto failure = budget.consume())
          return failure;
        auto address = bodyAddress(instance, step.outputBindings[j]);
        auto internal = regionAddress(instance, i, region.outputs[j].binding);
        values.emplace(address, Value{step.outputs[j], {internal}, {}});
      }
      continue;
    }
    if (step.kind != TypedStep::Kind::Query &&
        step.kind != TypedStep::Kind::Guard &&
        step.kind != TypedStep::Kind::Message)
      return error("math-placement-step-subset");
    if (step.kind == TypedStep::Kind::Query && !step.inputs.empty())
      return error("math-placement-query-subset");
    // Every effect is retained even if all of its results are discarded.
    for (const auto &input : step.inputs)
      if (auto failure =
              seed(bodyAddress(instance, input.binding), step.roles[0]))
        return failure;
    for (size_t j = 0; j < step.outputs.size(); ++j) {
      auto address = bodyAddress(instance, step.outputBindings[j]);
      Value value{step.outputs[j], {}, {}};
      if (step.kind == TypedStep::Kind::Message) {
        value.dependencies.push_back(
            bodyAddress(instance, step.inputs[0].binding));
        value.dependencyRole = instance.roles[step.roles[0]];
      }
      values.emplace(address, std::move(value));
      for (auto role : step.outputs[j].roles)
        if (auto failure = seed(address, role))
          return failure;
    }
  }
  if (const auto *ret = std::get_if<TypedReturn>(&body.terminal))
    for (size_t i = 0; i < ret->values.size(); ++i)
      for (auto role : body.results[i].roles)
        if (auto failure =
                seed(bodyAddress(instance, ret->values[i].binding), role))
          return failure;

  Demand result;
  // Iterative closure: graph size does not become native call-stack depth.
  while (!pending.empty()) {
    auto key = std::move(pending.back());
    pending.pop_back();
    if (!result.live.insert(key).second)
      continue;
    if (auto failure = budget.consume())
      return failure;
    const auto &value = values.at(key.source);
    bool available = false;
    for (auto localRole : value.port.roles) {
      if (auto failure = budget.consume())
        return failure;
      available |= instance.roles[localRole] == key.role;
    }
    if (!available)
      return error("math-placement-unavailable-component");
    if (!value.dependencyRole || *value.dependencyRole == key.role)
      for (const auto &dependency : value.dependencies) {
        if (auto failure = budget.consume())
          return failure;
        pending.push_back({dependency, key.role});
      }
  }
  return result;
}
} // namespace zkc::mathematical
