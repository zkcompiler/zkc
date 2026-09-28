#include "Admission.h"
#include "zkc/Support/Refusal.h"
#include <algorithm>
#include <limits>

using namespace llvm;
namespace zkc::mathematical {

Error AdmissionBuilder::push(Context &context, ArrayRef<Port> ports) {
  if (auto failure = budget.consume(ports.size()))
    return failure;
  for (const auto &port : ports)
    if (auto failure = budget.consume(port.roles.size()))
      return failure;
  size_t base = context.reversed.size();
  if (base > std::numeric_limits<uint32_t>::max() ||
      ports.size() > std::numeric_limits<uint32_t>::max() - base)
    return error("math-admission-limit");
  for (size_t i = ports.size(); i > 0; --i)
    context.reversed.push_back(
        {ports[i - 1], {static_cast<uint32_t>(base + i - 1)}});
  return Error::success();
}
Expected<std::vector<BindingId>>
AdmissionBuilder::latestBindings(const Context &context, size_t count) {
  if (count > context.reversed.size())
    return error("math-value-reference");
  if (auto failure = budget.consume(count))
    return failure;
  std::vector<BindingId> result;
  for (size_t i = 0; i < count; ++i)
    result.push_back(context.reversed[context.reversed.size() - 1 - i].id);
  return result;
}
Expected<Operand> AdmissionBuilder::operand(const Context &context,
                                            uint64_t index) {
  if (index >= context.reversed.size())
    return error("math-value-reference");
  const auto &binding = context.reversed[context.reversed.size() - 1 - index];
  if (auto failure = budget.consume(1 + binding.port.roles.size()))
    return failure;
  return Operand{static_cast<uint32_t>(index), binding.port, binding.id};
}
Expected<std::vector<Operand>>
AdmissionBuilder::operands(const Context &context,
                           ArrayRef<raw::ValueRef> input) {
  if (auto failure = budget.consume(input.size()))
    return failure;
  std::vector<Operand> result;
  for (auto ref : input) {
    auto value = operand(context, ref.index);
    if (!value)
      return value.takeError();
    result.push_back(std::move(*value));
  }
  return result;
}
Expected<std::vector<Operand>>
AdmissionBuilder::regionOperands(const Context &context,
                                 ArrayRef<raw::RegionRef> input) {
  if (auto failure = budget.consume(input.size()))
    return failure;
  std::vector<Operand> result;
  for (auto ref : input) {
    auto value = operand(context, ref.index);
    if (!value)
      return value.takeError();
    result.push_back(std::move(*value));
  }
  return result;
}
Error AdmissionBuilder::covers(const Operand &actual, const Port &required) {
  if (auto failure =
          budget.consume(1 + actual.port.roles.size() + required.roles.size()))
    return failure;
  if (actual.port.type != required.type)
    return error("math-operand-type");
  if (!std::includes(actual.port.roles.begin(), actual.port.roles.end(),
                     required.roles.begin(), required.roles.end()))
    return error("math-availability");
  return Error::success();
}
Error AdmissionBuilder::covers(ArrayRef<Operand> actual,
                               ArrayRef<Port> required) {
  if (actual.size() != required.size())
    return error("math-operand-arity");
  for (size_t i = 0; i < actual.size(); ++i)
    if (auto failure = covers(actual[i], required[i]))
      return failure;
  return Error::success();
}
Expected<AdmissionBuilder::Roles>
AdmissionBuilder::available(ArrayRef<Operand> input,
                            ArrayRef<uint32_t> parties) {
  if (auto failure = budget.consume(parties.size()))
    return failure;
  Roles result = parties.vec();
  for (const auto &operand : input) {
    if (auto failure =
            budget.consume(result.size() + operand.port.roles.size()))
      return failure;
    Roles intersection;
    std::set_intersection(result.begin(), result.end(),
                          operand.port.roles.begin(), operand.port.roles.end(),
                          std::back_inserter(intersection));
    result = std::move(intersection);
  }
  return result;
}
Expected<std::vector<Port>>
AdmissionBuilder::operandPorts(ArrayRef<Operand> inputs) {
  if (auto failure = budget.consume(inputs.size()))
    return failure;
  std::vector<Port> result;
  for (const auto &input : inputs) {
    if (auto failure = budget.consume(input.port.roles.size()))
      return failure;
    result.push_back(input.port);
  }
  return result;
}

Expected<TypedRegion>
AdmissionBuilder::region(const raw::Region &input, const Context &outer,
                         ArrayRef<Port> prefix, Parameters params,
                         ArrayRef<uint32_t> parties, unsigned depth) {
  if (auto failure = budget.consume(1 + input.nodes.size()))
    return failure;
  if (depth > 64)
    return error("math-region-depth");
  auto captures = operands(outer, input.captures);
  if (!captures)
    return captures.takeError();
  auto capturePorts = operandPorts(*captures);
  if (!capturePorts)
    return capturePorts.takeError();
  TypedRegion result;
  result.captures = std::move(*captures);
  for (const auto &port : prefix) {
    if (auto failure = budget.consume(1 + port.roles.size()))
      return failure;
    result.parameters.push_back(port);
  }
  result.parameters.insert(result.parameters.end(), capturePorts->begin(),
                           capturePorts->end());
  Context context;
  if (auto failure = push(context, result.parameters))
    return failure;
  auto parameters = latestBindings(context, result.parameters.size());
  if (!parameters)
    return parameters.takeError();
  result.parameterBindings = std::move(*parameters);
  for (const auto &item : input.nodes) {
    auto formed = node(item, context, params, parties, depth + 1);
    if (!formed)
      return atCoordinate(formed.takeError(), {AdmissionCoordinate::Node,
                                               uint32_t(result.nodes.size())});
    if (auto failure = push(context, formed->outputs))
      return failure;
    auto bindings = latestBindings(context, formed->outputs.size());
    if (!bindings)
      return bindings.takeError();
    formed->outputBindings = std::move(*bindings);
    result.nodes.push_back(std::move(*formed));
  }
  auto outputs = regionOperands(context, input.outputs);
  if (!outputs)
    return outputs.takeError();
  result.outputs = std::move(*outputs);
  return result;
}

Expected<TypedNode> AdmissionBuilder::node(const raw::PureNode &input,
                                           const Context &context,
                                           Parameters params,
                                           ArrayRef<uint32_t> parties,
                                           unsigned depth) {
  if (auto failure = budget.consume())
    return failure;
  TypedNode result{};
  if (const auto *op = std::get_if<raw::PureOperation>(&input)) {
    auto statics = substitute(op->statics, params);
    if (!statics)
      return statics.takeError();
    auto contract = operation(op->operation.index, *statics);
    if (!contract)
      return contract.takeError();
    if (contract->facts.purity != raw::Operation::Purity::Total)
      return error("math-purity");
    const auto &identity =
        source.manifest.operations[source.module.operations[op->operation.index]
                                       .identity.index];
    if (auto failure = registry.attributes(identity, *statics, op->attributes))
      return failure;
    auto inputs = regionOperands(context, op->arguments);
    if (!inputs)
      return inputs.takeError();
    if (inputs->size() != contract->signature.arguments.size())
      return error("math-operand-arity");
    for (size_t i = 0; i < inputs->size(); ++i)
      if ((*inputs)[i].port.type != contract->signature.arguments[i])
        return error("math-operand-type");
    auto availableRoles = available(*inputs, parties);
    if (!availableRoles)
      return availableRoles.takeError();
    result.kind = TypedNode::Kind::Operation;
    result.operation = static_cast<uint32_t>(op->operation.index);
    result.inputs = std::move(*inputs);
    result.outputs.push_back(
        {std::move(*availableRoles), contract->signature.result});
    result.statics = std::move(*statics);
    result.attributes = op->attributes;
    return result;
  }
  if (const auto *tuple = std::get_if<raw::Tuple>(&input)) {
    auto inputs = regionOperands(context, tuple->elements);
    if (!inputs)
      return inputs.takeError();
    std::vector<TypeId> elements;
    for (const auto &input : *inputs)
      elements.push_back(input.port.type);
    auto type = types.product(elements, budget);
    if (!type)
      return type.takeError();
    auto availableRoles = available(*inputs, parties);
    if (!availableRoles)
      return availableRoles.takeError();
    result.kind = TypedNode::Kind::Tuple;
    result.inputs = std::move(*inputs);
    result.outputs.push_back({std::move(*availableRoles), *type});
    return result;
  }
  if (const auto *projection = std::get_if<raw::Project>(&input)) {
    auto input = operand(context, projection->value.index);
    if (!input)
      return input.takeError();
    const auto *shape = types.get(input->port.type);
    if (!shape || shape->kind != TypeShape::Kind::Product ||
        projection->component >= shape->elements.size())
      return error("math-projection");
    result.kind = TypedNode::Kind::Project;
    result.component = projection->component;
    result.outputs.push_back(
        {input->port.roles, shape->elements[projection->component]});
    result.inputs.push_back(std::move(*input));
    return result;
  }
  const auto *map = std::get_if<raw::Map>(&input);
  const auto *fold = std::get_if<raw::Fold>(&input);
  if (!map && !fold)
    return error("math-pure-node");
  const auto &rawBody = map ? map->body : fold->body;
  if (!rawBody)
    return error("math-region-shape");
  auto count = normalize(map ? map->count : fold->count, params, budget);
  if (!count)
    return count.takeError();
  auto index = types.fin(*count, budget);
  if (!index)
    return index.takeError();
  std::vector<Port> prefix{{parties.vec(), *index}};
  std::vector<Port> initialPorts;
  if (fold) {
    auto inputs = regionOperands(context, fold->initial);
    if (!inputs)
      return inputs.takeError();
    auto initial = operandPorts(*inputs);
    if (!initial)
      return initial.takeError();
    initialPorts = std::move(*initial);
    prefix.insert(prefix.end(), initialPorts.begin(), initialPorts.end());
    result.inputs = std::move(*inputs);
  }
  auto inner = region(*rawBody, context, prefix, params, parties, depth + 1);
  if (!inner)
    return inner.takeError();
  if (map) {
    result.kind = TypedNode::Kind::Map;
    for (const auto &output : inner->outputs) {
      auto type = types.vector(output.port.type, *count, budget);
      if (!type)
        return type.takeError();
      result.outputs.push_back({output.port.roles, *type});
    }
  } else {
    result.kind = TypedNode::Kind::Fold;
    if (auto failure = covers(inner->outputs, initialPorts))
      return failure;
    for (size_t i = 0; i < initialPorts.size(); ++i)
      if (inner->outputs[i].port.roles != initialPorts[i].roles)
        return error("math-fold-availability");
    result.outputs = std::move(initialPorts);
  }
  result.statics.push_back(std::move(*count));
  result.body = std::make_shared<const TypedRegion>(std::move(*inner));
  return result;
}
} // namespace zkc::mathematical
