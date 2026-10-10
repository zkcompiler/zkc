#include "Checker.h"
#include "zkc/Contracts/Services.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
bool Checker::entries() {
  std::vector<unsigned> state(sources.size()), height(sources.size());
  auto visit = [&](auto &&self, DeclarationId id, unsigned depth) -> bool {
    auto &entry = output.declarations[id.index];
    if (state[id.index] == 2)
      return true;
    if (state[id.index] == 1)
      return types.fail("source.entry",
                        "complete Entry aliases must be acyclic", entry.span);
    if (depth > work.limits.callDepth || !types.charge(1, entry.span))
      return types.diagnostic
                 ? false
                 : types.fail("source.limit", "Entry alias depth exceeded",
                              entry.span);
    state[id.index] = 1;
    const auto &source = *sources[id.index];
    auto target = resolve(entry, source.target, source.span);
    if (!target)
      return false;
    const auto &definition = output.declarations[target->index];
    if (definition.kind == Declaration::Kind::Entry) {
      if (source.entryBlock || !source.targetArguments.empty())
        return types.fail(
            "source.entry",
            "complete Entry aliases cannot override or specialize choices",
            source.span);
      if (!self(self, *target, depth + 1))
        return false;
      if (source.entryKind != definition.entryKind())
        return types.fail("source.entry",
                          "Entry aliases must have the same run/proof kind",
                          source.span);
      uint64_t copied = definition.staticArguments.size();
      if (definition.proof()) {
        copied += definition.proof()->publicInputs.size() +
                  definition.proof()->acceptance.path.size();
        if (definition.proof()->completion)
          copied += definition.proof()->completion->path.size() + 1;
      }
      if (!types.charge(copied, source.span))
        return false;
      for (const auto &argument : definition.staticArguments)
        if (!types.chargeType(argument, source.span))
          return false;
      if (definition.proof() &&
          !types.charge(definition.proof()->suite.size(), source.span))
        return false;
      height[id.index] = height[target->index] + 1;
      entry.target = definition.target;
      entry.staticArguments = definition.staticArguments;
      entry.configuration = definition.configuration;
      for (const auto &slot : definition.setups) {
        if (!types.charge(slot.name.size() + slot.inputs.size() + 1,
                          source.span))
          return false;
        for (const auto &input : slot.inputs)
          if (!types.charge(input.path.size() + 1, source.span))
            return false;
      }
      entry.setups = definition.setups;
    } else if (definition.kind == Declaration::Kind::Protocol) {
      if (source.entryKind == EntryKind::Proof && !source.proof)
        return types.fail(
            "source.entry",
            "proof declarations require a proof configuration block",
            source.span);
      auto selected = arguments(entry, definition, source.targetArguments,
                                source.span, source.targetLabels);
      if (!selected)
        return false;
      height[id.index] = 1;
      entry.target = *target;
      entry.staticArguments = std::move(*selected);
      if (source.proof && !configureEntry(entry, definition, *source.proof))
        return false;
      if (!configureSetups(entry, definition, source.setups))
        return false;
    } else
      return types.fail("source.entry",
                        "entry target must be a protocol or complete Entry",
                        source.span);
    if (height[id.index] > work.limits.callDepth)
      return types.fail("source.limit", "Entry alias depth exceeded",
                        entry.span);
    state[id.index] = 2;
    return true;
  };
  for (unsigned i = 0; i < sources.size(); ++i)
    if (output.declarations[i].kind == Declaration::Kind::Entry &&
        !visit(visit, {i}, 1))
      return false;
  return true;
}
bool Checker::configureSetups(Declaration &entry, const Declaration &protocol,
                              ArrayRef<SyntaxSetupSlot> sources) {
  if (sources.size() > 64)
    return types.fail("source.limit", "Entry setup slot limit exceeded",
                      entry.span);
  auto bindings = types.substitution(protocol, entry.staticArguments);
  std::set<std::string> names;
  for (const auto &source : sources) {
    if (!types.charge(source.name.name.size() + source.inputs.size() + 1,
                      source.span))
      return false;
    if (!names.insert(source.name.name).second || source.inputs.empty())
      return types.fail("source.entry",
                        "setup slots must be named once and nonempty",
                        source.span);
    SetupSlot slot{source.name.name, {}, source.span};
    for (const auto &input : source.inputs) {
      if (!types.charge(protocol.inputs.size() + input.path.size() + 1,
                        input.span))
        return false;
      auto found = llvm::find_if(protocol.inputs, [&](const auto &port) {
        return port.name == input.port;
      });
      if (found == protocol.inputs.end())
        return types.fail("source.entry",
                          "setup selector names an absent input", input.span);
      EntryInput selected{
          unsigned(found - protocol.inputs.begin()), {}, input.span};
      auto current = types.substitute(found->type, bindings, input.span);
      if (!current)
        return false;
      for (const auto &name : input.path) {
        auto index = types.fieldIndex(entry, *current, name, input.span);
        if (!index)
          return false;
        current = types.projectedType(entry, std::move(*current), {*index},
                                      input.span);
        if (!current)
          return false;
        selected.path.push_back(*index);
      }
      slot.inputs.push_back(std::move(selected));
    }
    entry.setups.push_back(std::move(slot));
  }
  return true;
}
bool Checker::configureEntry(Declaration &entry, const Declaration &protocol,
                             const SyntaxProofEntry &source) {
  auto prover = roles(protocol, {source.prover.name}, source.prover.span);
  auto verifier = roles(protocol, {source.verifier.name}, source.verifier.span);
  if (!prover || !verifier)
    return false;
  ProofEntry value;
  value.construction = source.construction;
  value.prover = prover->front();
  value.verifier = verifier->front();
  value.suite = source.suite;
  value.span = source.span;
  auto portIndex = [&](const auto &ports,
                       const SyntaxName &name) -> std::optional<unsigned> {
    if (!types.charge(ports.size() + 1, name.span))
      return {};
    auto found = llvm::find_if(
        ports, [&](const auto &port) { return port.name == name.name; });
    if (found == ports.end()) {
      types.fail("source.entry", "Entry choice names an absent port or clause",
                 name.span);
      return {};
    }
    return found - ports.begin();
  };
  for (const auto &port : source.publicInputs) {
    auto index = portIndex(protocol.inputs, port);
    if (!index)
      return false;
    value.publicInputs.push_back(*index);
  }
  llvm::sort(value.publicInputs);
  if (std::adjacent_find(value.publicInputs.begin(),
                         value.publicInputs.end()) != value.publicInputs.end())
    return types.fail("source.entry", "duplicate public logical input",
                      source.span);
  auto bindings = types.substitution(protocol, entry.staticArguments);
  auto output = [&](const SyntaxSelector &source,
                    unsigned role) -> std::optional<SpecificationSelector> {
    auto index = portIndex(protocol.outputs, {source.port, source.span});
    if (!index)
      return {};
    SpecificationSelector selected{true, *index, role, {}, source.span};
    auto current =
        types.substitute(protocol.outputs[*index].type, bindings, source.span);
    if (!current)
      return {};
    for (const auto &name : source.path) {
      auto field = types.fieldIndex(entry, *current, name, source.span);
      if (!field)
        return {};
      current = types.projectedType(entry, std::move(*current), {*field},
                                    source.span);
      if (!current)
        return {};
      selected.path.push_back(*field);
    }
    return selected;
  };
  auto acceptance = output(source.acceptance, value.verifier);
  if (!acceptance)
    return false;
  value.acceptance = std::move(*acceptance);
  if (source.completion) {
    value.completion = output(*source.completion, value.prover);
    if (!value.completion)
      return false;
  }
  if (source.target) {
    value.target = portIndex(protocol.specifications, *source.target);
    if (!value.target)
      return false;
  }
  if (source.service) {
    value.service = portIndex(protocol.services, *source.service);
    if (!value.service)
      return false;
  }
  entry.configuration = std::move(value);
  return types.checkProofEntry(entry, protocol);
}

} // namespace zkc::language::detail
