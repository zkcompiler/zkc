#include "Demand.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Source/Codec.h"
#include "zkc/Support/Refusal.h"
#include <algorithm>

using namespace llvm;
namespace zkc::mathematical {
namespace {
std::string bindingName(BindingId binding, uint32_t role) {
  return "value_" + std::to_string(binding.ordinal) + "_role_" +
         std::to_string(role);
}
std::string siteName(uint64_t site) { return "effect_" + std::to_string(site); }
template <class T> source::Instruction instruction(std::string site, T value) {
  source::Instruction result;
  result.site = std::move(site);
  result.value = std::move(value);
  return result;
}
StringRef stopReason(raw::StopReason reason) {
  switch (reason) {
  case raw::StopReason::Reject:
    return "reject";
  case raw::StopReason::Abort:
    return "abort";
  case raw::StopReason::Exhausted:
    return "exhausted";
  case raw::StopReason::Incomplete:
    return "incomplete";
  case raw::StopReason::Refused:
    return "refused";
  }
  llvm_unreachable("admitted mathematical stop reason");
}

class Placer {
  const Subject &subject;
  const Installation &installation;
  const ClosedInstance &instance;
  const Demand &demand;
  AdmissionBudget &budget;
  const PlacementNames &names;
  source::Module target;
  source::Protocol protocol;
  PlacementWitness witness;
  std::map<ComponentKey, PlacedValue> values;
  std::map<uint32_t, std::string> types, operations, wires;

  const std::string &roleName(uint32_t role) const {
    return subject.source().module.roles.at(role);
  }
  std::string rootName(uint32_t root) const {
    return names.roots.empty() ? "root_" + std::to_string(root)
                               : names.roots[root];
  }
  std::string effectName(uint64_t site) const {
    auto found = names.sites.find(site);
    return found == names.sites.end() ? siteName(site) : found->second;
  }

  Expected<std::string> type(TypeId id) {
    if (auto found = types.find(id.ordinal()); found != types.end())
      return found->second;
    auto logical = installation.logicalType(id, subject.types(),
                                            subject.source().manifest);
    if (!logical)
      return logical.takeError();
    if (logical->kind != "field" && logical->kind != "group" &&
        logical->kind != "nonzero_field" && logical->kind != "bool")
      return error("math-placement-type-subset");
    auto name = logical->spelling();
    types.emplace(id.ordinal(), name);
    return name;
  }
  bool live(const SourceAddress &address, uint32_t role) const {
    return demand.live.count({address, role});
  }
  const PlacedValue &value(SourceAddress address, uint32_t role) const {
    return values.at({std::move(address), role});
  }
  void bind(SourceAddress address, uint32_t role, std::string name,
            std::vector<uint32_t> regions = {}) {
    values.emplace(ComponentKey{std::move(address), role},
                   PlacedValue{std::move(regions), std::move(name), {}});
  }
  Expected<std::string> operation(uint32_t index) {
    if (auto found = operations.find(index); found != operations.end())
      return found->second;
    auto name = "operation_" + std::to_string(index);
    const auto &raw = subject.source();
    const auto &identity =
        raw.manifest.operations[raw.module.operations[index].identity.index];
    const auto *binding = installation.binding(identity);
    if (!binding)
      return error("math-placement-operation-binding");
    source::OperationBinding declaration;
    declaration.name = name;
    declaration.application = *binding;
    target.bindings.push_back(std::move(declaration));
    operations.emplace(index, name);
    return name;
  }
  Error pure(const TypedStep &step, uint32_t stepIndex, uint32_t role) {
    if (auto failure = budget.consume(1 + step.outputBindings.size()))
      return failure;
    const auto &region = *step.region;
    bool used = false;
    for (auto binding : step.outputBindings)
      used |= live(bodyAddress(instance, binding), role);
    if (!used)
      return Error::success();
    source::Pure placed;
    placed.role = roleName(role);
    std::vector<uint32_t> path{static_cast<uint32_t>(protocol.body->size()), 0};
    std::set<std::string> captured;
    for (size_t i = 0; i < region.parameters.size(); ++i) {
      auto address =
          regionAddress(instance, stepIndex, region.parameterBindings[i]);
      if (!live(address, role))
        continue;
      if (auto failure = budget.consume())
        return failure;
      auto name =
          value(bodyAddress(instance, region.captures[i].binding), role).name;
      auto spelling = type(region.parameters[i].type);
      if (!spelling)
        return spelling.takeError();
      if (captured.insert(name).second)
        placed.captures.push_back({name, *spelling});
      bind(std::move(address), role, name, path);
    }
    for (size_t i = 0; i < region.nodes.size(); ++i) {
      const auto &node = region.nodes[i];
      auto address = regionAddress(instance, stepIndex, node.outputBindings[0]);
      if (!live(address, role))
        continue;
      if (auto failure = budget.consume(1 + node.inputs.size()))
        return failure;
      source::Names inputs;
      for (const auto &input : node.inputs)
        inputs.push_back(
            value(regionAddress(instance, stepIndex, input.binding), role)
                .name);
      auto name = "node_" + std::to_string(node.outputBindings[0].ordinal);
      auto callee = operation(*node.operation);
      if (!callee)
        return callee.takeError();
      placed.body.push_back(instruction(
          "pure_" + std::to_string(stepIndex) + "_role_" +
              std::to_string(role) + "_node_" + std::to_string(i),
          source::Operation{*callee, {}, {}, std::move(inputs), {name}}));
      bind(std::move(address), role, name, path);
    }
    source::Names yielded;
    for (size_t i = 0; i < step.outputs.size(); ++i) {
      auto address = bodyAddress(instance, step.outputBindings[i]);
      if (!live(address, role))
        continue;
      auto spelling = type(step.outputs[i].type);
      if (!spelling)
        return spelling.takeError();
      auto name = bindingName(step.outputBindings[i], role);
      placed.outputs.push_back({name, *spelling});
      yielded.push_back(
          value(regionAddress(instance, stepIndex, region.outputs[i].binding),
                role)
              .name);
      bind(std::move(address), role, name);
    }
    placed.body.push_back(instruction("", source::Yield{std::move(yielded)}));
    protocol.body->push_back(instruction("pure_" + std::to_string(stepIndex) +
                                             "_role_" + std::to_string(role),
                                         std::move(placed)));
    return Error::success();
  }
  Error roots() {
    std::map<uint32_t, std::string> services;
    for (uint32_t i = 0; i < subject.roots().size(); ++i) {
      if (auto failure = budget.consume())
        return failure;
      const auto &root = subject.roots()[i];
      auto service = root.signature.service;
      auto [found, inserted] =
          services.emplace(service, "service_" + std::to_string(service));
      if (inserted) {
        const auto &identity = subject.source().manifest.services[service];
        const auto *descriptor = installation.serviceBinding(identity);
        if (!descriptor)
          return error("math-placement-service-binding");
        source::OperationBinding binding;
        binding.name = found->second;
        binding.application = descriptor->transition;
        target.bindings.push_back(std::move(binding));
      }
      source::Root placed;
      placed.name = rootName(i);
      placed.service = found->second;
      for (auto owner : root.roles)
        placed.owners.push_back(roleName(owner));
      std::sort(placed.owners.begin(), placed.owners.end());
      witness.roots.emplace_back(i, placed.name);
      target.roots.push_back(std::move(placed));
    }
    return Error::success();
  }

public:
  Placer(const Subject &subject, const Installation &installation,
         const Demand &demand, AdmissionBudget &budget,
         const PlacementNames &names)
      : subject(subject), installation(installation),
        instance(subject.instances()[0]), demand(demand), budget(budget),
        names(names) {}

  Expected<std::pair<source::Module, PlacementWitness>> run() {
    const auto &body = instance.typed.body;
    if ((!names.arguments.empty() &&
         names.arguments.size() != body.parameters.size()) ||
        (!names.roots.empty() &&
         names.roots.size() != subject.roots().size()) ||
        (!names.wires.empty() &&
         names.wires.size() != subject.source().module.wires.size()))
      return error("math-placement-names");
    // Check all exercised port types, including discarded pure outputs. A
    // dead unsupported constructor must not silently expand this profile.
    for (const auto *ports : {&body.parameters, &body.results})
      for (const auto &port : *ports) {
        auto checked = type(port.type);
        if (!checked)
          return checked.takeError();
      }
    for (const auto &step : body.steps) {
      for (const auto &port : step.outputs) {
        auto checked = type(port.type);
        if (!checked)
          return checked.takeError();
      }
      if (step.region)
        for (const auto &node : step.region->nodes)
          for (const auto &port : node.outputs) {
            auto checked = type(port.type);
            if (!checked)
              return checked.takeError();
          }
    }
    witness.source = subject.digest().str();
    witness.definition = instance.definition;
    witness.protocol = names.protocol;
    witness.instance = names.instance;
    witness.statics = instance.statics;
    witness.roles = instance.roles;
    witness.capabilities = instance.roots;
    protocol.name = witness.protocol;
    protocol.body = source::Body{};
    for (auto role : instance.roles)
      protocol.roles.push_back(roleName(role));
    if (auto failure = roots())
      return failure;

    source::Names returned;
    // Role-major ports, preserving source port order inside each role. Module
    // roles may be a non-identity permutation of the local definition's roles.
    for (uint32_t role = 0; role < subject.source().module.roles.size();
         ++role) {
      for (size_t i = 0; i < body.parameters.size(); ++i) {
        auto address = bodyAddress(instance, body.parameterBindings[i]);
        if (!live(address, role))
          continue;
        auto name = names.arguments.empty()
                        ? bindingName(body.parameterBindings[i], role)
                        : names.arguments[i] + "_at_" + roleName(role);
        auto spelling = type(body.parameters[i].type);
        if (!spelling)
          return spelling.takeError();
        protocol.arguments.push_back({name, roleName(role), *spelling});
        bind(std::move(address), role, name);
      }
    }
    for (uint32_t i = 0; i < body.steps.size(); ++i) {
      if (auto failure = budget.consume())
        return failure;
      const auto &step = body.steps[i];
      if (step.kind == TypedStep::Kind::Pure) {
        for (uint32_t role = 0; role < subject.source().module.roles.size();
             ++role)
          if (auto failure = pure(step, i, role))
            return failure;
        continue;
      }
      auto owner = instance.roles[step.roles[0]];
      auto site = effectName(*step.site);
      if (step.kind == TypedStep::Kind::Query) {
        auto root = instance.roots[step.capabilities[0]];
        auto name = bindingName(step.outputBindings[0], owner);
        protocol.body->push_back(instruction(
            site, source::Query{roleName(owner), rootName(root), {}, {name}}));
        bind(bodyAddress(instance, step.outputBindings[0]), owner, name);
        witness.sites.push_back({*step.site, site, "query"});
      } else if (step.kind == TypedStep::Kind::Guard) {
        protocol.body->push_back(instruction(
            site,
            source::Guard{
                roleName(owner),
                value(bodyAddress(instance, step.inputs[0].binding), owner)
                    .name}));
        witness.sites.push_back({*step.site, site, "guard"});
      } else {
        assert(step.kind == TypedStep::Kind::Message);
        auto wire = *step.declaration;
        const auto &raw = subject.source();
        const auto &identity =
            raw.manifest.wires[raw.module.wires[wire].identity.index];
        auto payload = installation.logicalType(step.outputs[0].type,
                                                subject.types(), raw.manifest);
        if (!payload)
          return payload.takeError();
        const auto *wireBinding = installation.wireBinding(identity);
        if (!wireBinding || !wireBinding->implicitDefault ||
            !(wireBinding->payload == *payload))
          return error("math-placement-wire-realization");
        auto schema = names.wires.empty() ? "wire_" + std::to_string(wire)
                                          : names.wires[wire];
        wires.emplace(wire, schema);
        auto receiver = instance.roles[step.roles[1]];
        auto name = bindingName(step.outputBindings[0], receiver);
        auto sent =
            value(bodyAddress(instance, step.inputs[0].binding), owner).name;
        protocol.body->push_back(
            instruction(site, source::Message{schema, roleName(owner),
                                              roleName(receiver), sent, name}));
        bind(bodyAddress(instance, step.outputBindings[0]), owner, sent);
        bind(bodyAddress(instance, step.outputBindings[0]), receiver, name);
        witness.sites.push_back({*step.site, site, "message"});
      }
    }
    for (uint32_t role = 0; role < subject.source().module.roles.size();
         ++role) {
      uint32_t portIndex = 0;
      for (uint32_t i = 0; i < body.results.size(); ++i) {
        const auto &port = body.results[i];
        if (llvm::none_of(port.roles, [&](uint32_t local) {
              return instance.roles[local] == role;
            }))
          continue;
        auto spelling = type(port.type);
        if (!spelling)
          return spelling.takeError();
        protocol.results.push_back({roleName(role), *spelling});
        witness.results.push_back({role, i, portIndex++});
        if (const auto *ret = std::get_if<TypedReturn>(&body.terminal))
          returned.push_back(
              value(bodyAddress(instance, ret->values[i].binding), role).name);
      }
    }
    if (const auto *stop = std::get_if<TypedStop>(&body.terminal)) {
      auto site = effectName(stop->site);
      protocol.body->push_back(
          instruction(site, source::Stop{roleName(instance.roles[stop->owner]),
                                         stopReason(stop->reason).str()}));
      witness.sites.push_back({stop->site, site, "stop"});
    } else {
      protocol.body->push_back(
          instruction("", source::Return{std::move(returned)}));
    }
    for (const auto &key : demand.live) {
      if (auto failure = budget.consume())
        return failure;
      witness.components.push_back({key, values.at(key)});
    }
    witness.operations.assign(operations.begin(), operations.end());
    witness.wires.assign(wires.begin(), wires.end());
    source::Instance placedInstance;
    placedInstance.name = witness.instance;
    placedInstance.protocol = protocol.name;
    for (const auto &role : protocol.roles)
      placedInstance.roles.emplace_back(role, role);
    target.protocols.push_back(std::move(protocol));
    target.instances.push_back(std::move(placedInstance));
    source::Entry entry;
    entry.name = names.entry;
    entry.instance = witness.instance;
    target.entries.push_back(std::move(entry));
    if (auto failure = source::checkStructure(target))
      return failure;
    if (auto failure = protocol::admit(target, true))
      return failure;
    auto digest = placementTargetDigest(target);
    if (!digest)
      return digest.takeError();
    witness.target = std::move(*digest);
    return std::make_pair(std::move(target), std::move(witness));
  }
};
} // namespace

Expected<Placement> place(const Subject &input,
                          const Installation &installation,
                          AdmissionBudget budget) {
  return place(input.source(), installation, budget);
}

Expected<Placement> place(const raw::Subject &input,
                          const Installation &installation,
                          AdmissionBudget budget, const PlacementNames &names) {
  auto subject = admit(input, installation, budget);
  if (!subject)
    return subject.takeError();
  auto demand = computeDemand(*subject, budget);
  if (!demand)
    return demand.takeError();
  auto placed = Placer(*subject, installation, *demand, budget, names).run();
  if (!placed)
    return placed.takeError();
  // Witnesses use the same canonical tree resource bounds as other math data.
  auto encoded = encode(placed->second);
  if (!encoded)
    return encoded.takeError();
  return Placement{std::move(*subject),
                   source::Document(std::move(placed->first)),
                   std::move(placed->second)};
}
} // namespace zkc::mathematical
