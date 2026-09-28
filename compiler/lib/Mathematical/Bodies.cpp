#include "Admission.h"
#include "zkc/Support/Refusal.h"
#include <algorithm>

using namespace llvm;
namespace zkc::mathematical {

Error AdmissionBuilder::effectSite(uint64_t actual, uint64_t &expected) {
  if (auto failure = budget.consume())
    return failure;
  if (actual != expected)
    return error("math-site-order");
  ++expected;
  return Error::success();
}
Expected<std::vector<Port>>
AdmissionBuilder::mapPorts(ArrayRef<Port> ports, ArrayRef<uint32_t> mapping) {
  if (auto failure = budget.consume(ports.size()))
    return failure;
  std::vector<Port> result;
  for (const auto &port : ports) {
    if (auto failure = budget.consume(port.roles.size()))
      return failure;
    Roles roles;
    for (auto role : port.roles) {
      if (role >= mapping.size())
        return error("math-role-binding");
      roles.push_back(mapping[role]);
    }
    std::sort(roles.begin(), roles.end());
    result.push_back({std::move(roles), port.type});
  }
  return result;
}
Error AdmissionBuilder::checkCapabilities(
    ArrayRef<raw::CapabilityPortRef> bindings, ArrayRef<Permission> actual,
    ArrayRef<Permission> expected, ArrayRef<uint32_t> roleMap) {
  if (bindings.size() != expected.size())
    return error("math-capability-arity");
  for (size_t i = 0; i < bindings.size(); ++i) {
    if (auto failure = budget.consume())
      return failure;
    if (bindings[i].index >= actual.size())
      return error("math-capability-reference");
    const auto &permission = actual[bindings[i].index];
    if (!(permission.signature == expected[i].signature))
      return error("math-capability-signature");
    for (auto role : expected[i].roles) {
      if (auto failure = budget.consume())
        return failure;
      if (role >= roleMap.size() ||
          !std::binary_search(permission.roles.begin(), permission.roles.end(),
                              roleMap[role]))
        return error("math-capability-permission");
    }
  }
  return Error::success();
}
Expected<TypedDefinition> AdmissionBuilder::definition(uint32_t index,
                                                       Parameters params) {
  const auto &input = source.module.definitions[index];
  auto declared = signature(index, params);
  if (!declared)
    return declared.takeError();
  auto partyList = parties(declared->roles);
  if (!partyList)
    return partyList.takeError();
  Context arguments;
  if (auto failure = push(arguments, declared->arguments))
    return failure;
  std::vector<TypedRelationBinding> relations;
  for (const auto &binding : input.relations) {
    if (binding.relation.index >= source.module.relations.size())
      return error("math-relation-reference");
    const auto &relation = source.module.relations[binding.relation.index];
    if (binding.statics.size() != relation.statics)
      return error("math-static-arity");
    auto statics = substitute(binding.statics, params);
    if (!statics)
      return statics.takeError();
    auto publicTypes = typeList(relation.publicInputs, *statics);
    if (!publicTypes)
      return publicTypes.takeError();
    auto witnessTypes = typeList(relation.witnessInputs, *statics);
    if (!witnessTypes)
      return witnessTypes.takeError();
    auto publicInputs = operands(arguments, binding.publicInputs);
    if (!publicInputs)
      return publicInputs.takeError();
    auto witnessInputs = operands(arguments, binding.witnessInputs);
    if (!witnessInputs)
      return witnessInputs.takeError();
    std::vector<Port> publicPorts, witnessPorts, evaluatorPorts;
    for (auto type : *publicTypes) {
      publicPorts.push_back({{}, type});
      evaluatorPorts.push_back({{0}, type});
    }
    for (auto type : *witnessTypes) {
      witnessPorts.push_back({{}, type});
      evaluatorPorts.push_back({{0}, type});
    }
    if (auto failure = covers(*publicInputs, publicPorts))
      return failure;
    if (auto failure = covers(*witnessInputs, witnessPorts))
      return failure;
    Context evaluator;
    if (auto failure = push(evaluator, evaluatorPorts))
      return failure;
    auto predicate = region(relation.body, evaluator, {}, *statics, {0}, 0);
    if (!predicate)
      return predicate.takeError();
    if (predicate->outputs.size() != 1 ||
        !types.isCondition(predicate->outputs[0].port.type))
      return error("math-relation-result");
    relations.push_back({static_cast<uint32_t>(binding.relation.index),
                         std::move(*statics), std::move(*publicInputs),
                         std::move(*witnessInputs)});
  }
  uint64_t site = 0;
  auto formed = body(input.body, declared->arguments, declared->results, params,
                     *partyList, declared->capabilities, index, site, 0);
  if (!formed)
    return atCoordinate(formed.takeError(),
                        {AdmissionCoordinate::Definition, index});
  return TypedDefinition{input.statics,
                         declared->roles,
                         std::move(declared->capabilities),
                         std::move(declared->arguments),
                         std::move(declared->results),
                         std::move(relations),
                         std::move(*formed)};
}
Expected<TypedBody>
AdmissionBuilder::body(const raw::Body &input, ArrayRef<Port> arguments,
                       ArrayRef<Port> results, Parameters params,
                       ArrayRef<uint32_t> parties,
                       ArrayRef<Permission> permissions, uint32_t definition,
                       uint64_t &site, unsigned depth) {
  if (auto failure = budget.consume(1 + input.steps.size()))
    return failure;
  if (depth > 64)
    return error("math-body-depth");
  Context context;
  if (auto failure = push(context, arguments))
    return failure;
  auto parameters = latestBindings(context, arguments.size());
  if (!parameters)
    return parameters.takeError();
  TypedBody result{arguments.vec(),
                   results.vec(),
                   {},
                   TypedReturn{},
                   std::move(*parameters)};
  for (const auto &item : input.steps) {
    auto formed = step(item, context, params, parties, permissions, definition,
                       site, depth + 1);
    if (!formed)
      return atCoordinate(formed.takeError(), {AdmissionCoordinate::Step,
                                               uint32_t(result.steps.size())});
    if (auto failure = push(context, formed->outputs))
      return failure;
    auto bindings = latestBindings(context, formed->outputs.size());
    if (!bindings)
      return bindings.takeError();
    formed->outputBindings = std::move(*bindings);
    result.steps.push_back(std::move(*formed));
  }
  if (const auto *ret = std::get_if<raw::Return>(&input.terminal)) {
    auto values = operands(context, ret->values);
    if (!values)
      return atCoordinate(values.takeError(),
                          {AdmissionCoordinate::Terminal, 0});
    if (auto failure = covers(*values, results))
      return atCoordinate(std::move(failure),
                          {AdmissionCoordinate::Terminal, 0});
    result.terminal = TypedReturn{std::move(*values)};
  } else if (const auto *stop = std::get_if<raw::Stop>(&input.terminal)) {
    if (auto failure = effectSite(stop->site, site))
      return failure;
    if (stop->owner.index >= parties.size())
      return error("math-owner");
    result.terminal = TypedStop{
        stop->site, static_cast<uint32_t>(stop->owner.index), stop->reason};
  } else
    return error("math-terminal");
  return result;
}

Expected<TypedStep>
AdmissionBuilder::step(const raw::Step &input, const Context &context,
                       Parameters params, ArrayRef<uint32_t> parties,
                       ArrayRef<Permission> permissions, uint32_t definition,
                       uint64_t &site, unsigned depth) {
  if (auto failure = budget.consume())
    return failure;
  TypedStep result{};
  if (const auto *pure = std::get_if<raw::Pure>(&input)) {
    auto formed = region(pure->region, context, {}, params, parties, 0);
    if (!formed)
      return formed.takeError();
    auto outputs = operandPorts(formed->outputs);
    if (!outputs)
      return outputs.takeError();
    result.kind = TypedStep::Kind::Pure;
    result.outputs = std::move(*outputs);
    result.region = std::make_shared<const TypedRegion>(std::move(*formed));
    return result;
  }
  auto start = [&](uint64_t actual, TypedStep::Kind kind) -> Error {
    if (auto failure = effectSite(actual, site))
      return failure;
    result.kind = kind;
    result.site = actual;
    return Error::success();
  };
  auto owner = [&](raw::Role role) -> Error {
    if (role.index >= parties.size())
      return error("math-owner");
    result.roles.push_back(static_cast<uint32_t>(role.index));
    return Error::success();
  };
  auto localArguments = [&](ArrayRef<raw::ValueRef> refs,
                            ArrayRef<TypeId> required,
                            uint32_t self) -> Expected<std::vector<Operand>> {
    auto values = operands(context, refs);
    if (!values)
      return values.takeError();
    if (values->size() != required.size())
      return error("math-operand-arity");
    for (size_t i = 0; i < values->size(); ++i)
      if (auto failure = covers((*values)[i], {{self}, required[i]}))
        return failure;
    return values;
  };
  if (const auto *local = std::get_if<raw::Local>(&input)) {
    if (auto failure = start(local->site, TypedStep::Kind::Local))
      return failure;
    if (auto failure = owner(local->owner))
      return failure;
    auto statics = substitute(local->statics, params);
    if (!statics)
      return statics.takeError();
    auto contract = operation(local->operation.index, *statics);
    if (!contract)
      return contract.takeError();
    if (contract->facts.purity != raw::Operation::Purity::Ordered)
      return error("math-purity");
    auto self = static_cast<uint32_t>(local->owner.index);
    if (local->capabilities.size() != contract->signature.capabilities.size())
      return error("math-capability-arity");
    for (size_t i = 0; i < local->capabilities.size(); ++i) {
      auto index = local->capabilities[i].index;
      if (index >= permissions.size())
        return error("math-capability-reference");
      if (!(permissions[index].signature ==
            contract->signature.capabilities[i]))
        return error("math-capability-signature");
      if (!std::binary_search(permissions[index].roles.begin(),
                              permissions[index].roles.end(), self))
        return error("math-capability-permission");
      result.capabilities.push_back(static_cast<uint32_t>(index));
    }
    const auto &identity =
        source.manifest.operations
            [source.module.operations[local->operation.index].identity.index];
    if (auto failure =
            registry.attributes(identity, *statics, local->attributes))
      return failure;
    auto values =
        localArguments(local->arguments, contract->signature.arguments, self);
    if (!values)
      return values.takeError();
    result.declaration = static_cast<uint32_t>(local->operation.index);
    result.statics = std::move(*statics);
    result.attributes = local->attributes;
    result.inputs = std::move(*values);
    result.outputs.push_back({{self}, contract->signature.result});
    return result;
  }
  if (const auto *query = std::get_if<raw::Query>(&input)) {
    if (auto failure = start(query->site, TypedStep::Kind::Query))
      return failure;
    if (auto failure = owner(query->owner))
      return failure;
    auto index = query->capability.index;
    if (index >= permissions.size())
      return error("math-capability-reference");
    auto self = static_cast<uint32_t>(query->owner.index);
    if (!std::binary_search(permissions[index].roles.begin(),
                            permissions[index].roles.end(), self))
      return error("math-capability-permission");
    auto values = localArguments(query->arguments,
                                 permissions[index].signature.arguments, self);
    if (!values)
      return values.takeError();
    result.capabilities.push_back(static_cast<uint32_t>(index));
    result.inputs = std::move(*values);
    result.outputs.push_back({{self}, permissions[index].signature.result});
    return result;
  }
  if (const auto *guard = std::get_if<raw::Guard>(&input)) {
    if (auto failure = start(guard->site, TypedStep::Kind::Guard))
      return failure;
    if (auto failure = owner(guard->owner))
      return failure;
    auto value = operand(context, guard->condition.index);
    if (!value)
      return value.takeError();
    if (!types.isCondition(value->port.type))
      return error("math-condition-type");
    if (auto failure =
            covers(*value, {{static_cast<uint32_t>(guard->owner.index)},
                            value->port.type}))
      return failure;
    result.inputs.push_back(std::move(*value));
    return result;
  }
  if (const auto *message = std::get_if<raw::Message>(&input)) {
    if (auto failure = start(message->site, TypedStep::Kind::Message))
      return failure;
    if (auto failure = owner(message->sender))
      return failure;
    if (auto failure = owner(message->receiver))
      return failure;
    if (message->sender.index == message->receiver.index)
      return error("math-message-roles");
    auto statics = substitute(message->statics, params);
    if (!statics)
      return statics.takeError();
    auto payload = wire(message->wire.index, *statics);
    if (!payload)
      return payload.takeError();
    auto value = operand(context, message->value.index);
    if (!value)
      return value.takeError();
    if (auto failure = covers(
            *value, {{static_cast<uint32_t>(message->sender.index)}, *payload}))
      return failure;
    result.statics = std::move(*statics);
    result.declaration = static_cast<uint32_t>(message->wire.index);
    result.inputs.push_back(std::move(*value));
    Roles availability = result.roles;
    std::sort(availability.begin(), availability.end());
    result.outputs.push_back({std::move(availability), *payload});
    return result;
  }
  if (const auto *call = std::get_if<raw::Invoke>(&input)) {
    if (auto failure = start(call->site, TypedStep::Kind::Invoke))
      return failure;
    if (call->definition.index >= definition)
      return error("math-earlier-definition");
    auto statics = substitute(call->statics, params);
    if (!statics)
      return statics.takeError();
    auto callee = signature(call->definition.index, *statics);
    if (!callee)
      return callee.takeError();
    auto roleMap = roles(call->roles, parties.size(), false);
    if (!roleMap)
      return roleMap.takeError();
    if (roleMap->size() != callee->roles)
      return error("math-role-arity");
    if (auto failure = checkCapabilities(call->capabilities, permissions,
                                         callee->capabilities, *roleMap))
      return failure;
    auto expected = mapPorts(callee->arguments, *roleMap);
    if (!expected)
      return expected.takeError();
    auto outputs = mapPorts(callee->results, *roleMap);
    if (!outputs)
      return outputs.takeError();
    auto values = operands(context, call->arguments);
    if (!values)
      return values.takeError();
    if (auto failure = covers(*values, *expected))
      return failure;
    result.declaration = static_cast<uint32_t>(call->definition.index);
    result.statics = std::move(*statics);
    result.roles = std::move(*roleMap);
    for (auto capability : call->capabilities)
      result.capabilities.push_back(static_cast<uint32_t>(capability.index));
    result.inputs = std::move(*values);
    result.outputs = std::move(*outputs);
    return result;
  }
  const auto *repeat = std::get_if<raw::Repeat>(&input);
  if (!repeat || !repeat->body)
    return error("math-step");
  if (auto failure = start(repeat->site, TypedStep::Kind::Repeat))
    return failure;
  auto count = normalize(repeat->count, params, budget);
  if (!count)
    return count.takeError();
  auto carried = ports(repeat->carried, params, parties.size());
  if (!carried)
    return carried.takeError();
  auto initial = operands(context, repeat->initial);
  if (!initial)
    return initial.takeError();
  if (auto failure = covers(*initial, *carried))
    return failure;
  auto captures = operands(context, repeat->captures);
  if (!captures)
    return captures.takeError();
  auto capturePorts = operandPorts(*captures);
  if (!capturePorts)
    return capturePorts.takeError();
  auto index = types.fin(*count, budget);
  if (!index)
    return index.takeError();
  std::vector<Port> arguments{{parties.vec(), *index}};
  arguments.insert(arguments.end(), carried->begin(), carried->end());
  arguments.insert(arguments.end(), capturePorts->begin(), capturePorts->end());
  auto inner = body(*repeat->body, arguments, *carried, params, parties,
                    permissions, definition, site, depth + 1);
  if (!inner)
    return inner.takeError();
  result.statics.push_back(std::move(*count));
  result.inputs = std::move(*initial);
  result.outputs = std::move(*carried);
  result.captures = std::move(*captures);
  result.body = std::make_shared<const TypedBody>(std::move(*inner));
  return result;
}
} // namespace zkc::mathematical
