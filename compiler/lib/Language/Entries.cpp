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
      return fail("source.entry", "complete Entry aliases must be acyclic",
                  entry.span);
    if (depth > work.limits.callDepth || !charge(1, entry.span))
      return diagnostic ? false
                        : fail("source.limit", "Entry alias depth exceeded",
                               entry.span);
    state[id.index] = 1;
    const auto &source = *sources[id.index];
    auto target = resolve(entry, source.target, source.span);
    if (!target)
      return false;
    const auto &definition = output.declarations[target->index];
    if (definition.kind == Declaration::Kind::Entry) {
      if (source.entryBlock || !source.targetArguments.empty())
        return fail(
            "source.entry",
            "complete Entry aliases cannot override or specialize choices",
            source.span);
      if (!self(self, *target, depth + 1))
        return false;
      uint64_t copied = definition.staticArguments.size();
      if (definition.proof) {
        copied += definition.proof->publicInputs.size() +
                  definition.proof->acceptance.path.size();
        if (definition.proof->completion)
          copied += definition.proof->completion->path.size() + 1;
      }
      if (!charge(copied, source.span))
        return false;
      for (const auto &argument : definition.staticArguments)
        if (!chargeType(argument, source.span))
          return false;
      if (definition.proof &&
          !charge(definition.proof->suite.size(), source.span))
        return false;
      height[id.index] = height[target->index] + 1;
      entry.target = definition.target;
      entry.staticArguments = definition.staticArguments;
      entry.proof = definition.proof;
      for (const auto &slot : definition.setups) {
        if (!charge(slot.name.size() + slot.inputs.size() + 1, source.span))
          return false;
        for (const auto &input : slot.inputs)
          if (!charge(input.path.size() + 1, source.span))
            return false;
      }
      entry.setups = definition.setups;
    } else if (definition.kind == Declaration::Kind::Protocol) {
      auto selected =
          arguments(entry, definition, source.targetArguments, source.span);
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
      return fail("source.entry",
                  "entry target must be a protocol or complete Entry",
                  source.span);
    if (height[id.index] > work.limits.callDepth)
      return fail("source.limit", "Entry alias depth exceeded", entry.span);
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
    return fail("source.limit", "Entry setup slot limit exceeded", entry.span);
  auto bindings = substitution(protocol, entry.staticArguments);
  std::set<std::string> names;
  for (const auto &source : sources) {
    if (!charge(source.name.name.size() + source.inputs.size() + 1,
                source.span))
      return false;
    if (!names.insert(source.name.name).second || source.inputs.empty())
      return fail("source.entry", "setup slots must be named once and nonempty",
                  source.span);
    SetupSlot slot{source.name.name, {}, source.span};
    for (const auto &input : source.inputs) {
      if (!charge(protocol.inputs.size() + input.path.size() + 1, input.span))
        return false;
      auto found = llvm::find_if(protocol.inputs, [&](const auto &port) {
        return port.name == input.port;
      });
      if (found == protocol.inputs.end())
        return fail("source.entry", "setup selector names an absent input",
                    input.span);
      EntryInput selected{
          unsigned(found - protocol.inputs.begin()), {}, input.span};
      auto current = substitute(found->type, bindings, input.span);
      if (!current)
        return false;
      for (const auto &name : input.path) {
        auto index = fieldIndex(entry, *current, name, input.span);
        if (!index)
          return false;
        current =
            projectedType(entry, std::move(*current), {*index}, input.span);
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
    if (!charge(ports.size() + 1, name.span))
      return {};
    auto found = llvm::find_if(
        ports, [&](const auto &port) { return port.name == name.name; });
    if (found == ports.end()) {
      fail("source.entry", "Entry choice names an absent port or clause",
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
    return fail("source.entry", "duplicate public logical input", source.span);
  auto bindings = substitution(protocol, entry.staticArguments);
  auto output = [&](const SyntaxSelector &source,
                    unsigned role) -> std::optional<SpecificationSelector> {
    auto index = portIndex(protocol.outputs, {source.port, source.span});
    if (!index)
      return {};
    SpecificationSelector selected{true, *index, role, {}, source.span};
    auto current =
        substitute(protocol.outputs[*index].type, bindings, source.span);
    if (!current)
      return {};
    for (const auto &name : source.path) {
      auto field = fieldIndex(entry, *current, name, source.span);
      if (!field)
        return {};
      current =
          projectedType(entry, std::move(*current), {*field}, source.span);
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
  entry.proof = std::move(value);
  return checkProofEntry(entry, protocol);
}
bool Checker::checkProofEntry(const Declaration &entry,
                              const Declaration &protocol) {
  if (!entry.proof)
    return true;
  const auto &value = *entry.proof;
  if (!charge(protocol.inputs.size() + protocol.services.size() +
                  value.publicInputs.size() + value.acceptance.path.size() + 1,
              value.span))
    return false;
  if (protocol.roles.size() != 2 || value.prover >= protocol.roles.size() ||
      value.verifier >= protocol.roles.size() || value.prover == value.verifier)
    return fail("source.entry",
                "proof Entry requires two distinct participants", value.span);
  std::vector<unsigned> required;
  for (unsigned i = 0; i < protocol.inputs.size(); ++i)
    if (is_contained(protocol.inputs[i].roles, value.verifier))
      required.push_back(i);
  if (required != value.publicInputs)
    return fail("source.entry",
                "public inputs must exactly authorize verifier data ports",
                value.span);
  auto bindings = substitution(protocol, entry.staticArguments);
  auto booleanOutput = [&](const SpecificationSelector &selected, unsigned role,
                           StringRef keyword) {
    if (!charge(selected.path.size() + 1, selected.span))
      return false;
    if (!selected.output || selected.role != role ||
        selected.port >= protocol.outputs.size() ||
        !is_contained(protocol.outputs[selected.port].roles, role))
      return fail("source.entry",
                  (keyword + " result is unavailable at its participant").str(),
                  selected.span);
    auto type = substitute(protocol.outputs[selected.port].type, bindings,
                           selected.span);
    if (!type)
      return false;
    type = projectedType(entry, std::move(*type), selected.path, selected.span);
    if (!type)
      return false;
    return type->kind == Type::Kind::Boolean ||
           fail("source.entry",
                (keyword + " must select a Boolean output").str(),
                selected.span);
  };
  const auto &acceptance = value.acceptance;
  if (!booleanOutput(acceptance, value.verifier, "accept") ||
      (value.completion &&
       !booleanOutput(*value.completion, value.prover, "complete")))
    return false;
  if (value.construction == ProofEntry::Construction::Authored) {
    if (!value.suite.empty() || value.service)
      return fail("source.entry",
                  "authored construction cannot derive a service", value.span);
  } else {
    auto field = protocol::nativeChallengeField(value.suite);
    if (field.empty() || !value.service ||
        *value.service >= protocol.services.size() ||
        protocol.services[*value.service].owner != value.verifier)
      return fail("source.entry",
                  "construction requires an installed suite and matching "
                  "verifier service",
                  value.span);
    auto selected = substitute(protocol.services[*value.service].field,
                               bindings, value.span);
    if (!selected)
      return false;
    if (selected->kind != Type::Kind::Field || selected->domain != field)
      return fail("source.entry", "construction field differs from service",
                  value.span);
  }
  for (unsigned i = 0; i < protocol.services.size(); ++i)
    if (protocol.services[i].owner == value.verifier && value.service != i)
      return fail("source.entry",
                  "verifier services must belong to the selected construction",
                  protocol.services[i].span);
  if (value.target) {
    if (*value.target >= protocol.specifications.size())
      return fail("source.entry", "selected target is absent", value.span);
    const auto &clause = protocol.specifications[*value.target];
    if (clause.kind != SpecificationClause::Kind::Target || !clause.decision ||
        clause.decision->port != acceptance.port ||
        clause.decision->path != acceptance.path ||
        clause.decision->role != value.verifier)
      return fail("source.entry",
                  "selected target must use the Entry acceptance", clause.span);
    const auto &relation = output.declarations[clause.subject.relation.index];
    for (auto [operand, purpose] :
         zip(clause.subject.operands, relation.relation->purposes)) {
      if (!charge(operand.path.size() + 1, operand.span))
        return false;
      if (operand.output || operand.port >= protocol.inputs.size())
        return fail("source.entry",
                    "native statement export requires entry inputs",
                    operand.span);
      bool visible =
          is_contained(protocol.inputs[operand.port].roles, value.verifier);
      if ((purpose == RelationPurpose::Witness) == visible)
        return fail("source.entry",
                    "target purpose disagrees with verifier input availability",
                    operand.span);
    }
  }
  return true;
}
} // namespace zkc::language::detail
