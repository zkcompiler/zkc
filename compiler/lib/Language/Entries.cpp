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
      if (source.proof || !source.targetArguments.empty())
        return fail(
            "source.entry",
            "complete Entry aliases cannot override or specialize choices",
            source.span);
      if (!self(self, *target, depth + 1) ||
          !charge(definition.staticArguments.size() +
                      (definition.proof
                           ? definition.proof->publicInputs.size() +
                                 definition.proof->acceptance.path.size()
                           : 0),
                  source.span))
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
bool Checker::configureEntry(Declaration &entry, const Declaration &protocol,
                             const SyntaxProofEntry &source) {
  auto prover = roles(protocol, {source.prover.name}, source.prover.span);
  auto verifier = roles(protocol, {source.verifier.name}, source.verifier.span);
  if (!prover || !verifier)
    return false;
  ProofEntry value{source.construction,
                   prover->front(),
                   verifier->front(),
                   {},
                   {true, 0, verifier->front(), {}, source.acceptance.span},
                   {},
                   {},
                   source.suite,
                   source.span};
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
  auto index = portIndex(protocol.outputs,
                         {source.acceptance.port, source.acceptance.span});
  if (!index)
    return false;
  value.acceptance.port = *index;
  auto bindings = substitution(protocol, entry.staticArguments);
  auto current = substitute(protocol.outputs[*index].type, bindings,
                            source.acceptance.span);
  if (!current)
    return false;
  for (const auto &name : source.acceptance.path) {
    auto field = fieldIndex(entry, *current, name, source.acceptance.span);
    if (!field)
      return false;
    current = projectedType(entry, std::move(*current), {*field},
                            source.acceptance.span);
    if (!current)
      return false;
    value.acceptance.path.push_back(*field);
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
  const auto &acceptance = value.acceptance;
  if (!acceptance.output || acceptance.role != value.verifier ||
      acceptance.port >= protocol.outputs.size() ||
      !is_contained(protocol.outputs[acceptance.port].roles, value.verifier))
    return fail("source.entry", "acceptance is unavailable at the verifier",
                acceptance.span);
  auto bindings = substitution(protocol, entry.staticArguments);
  auto type = substitute(protocol.outputs[acceptance.port].type, bindings,
                         acceptance.span);
  if (!type)
    return false;
  type =
      projectedType(entry, std::move(*type), acceptance.path, acceptance.span);
  if (!type)
    return false;
  if (type->kind != Type::Kind::Boolean)
    return fail("source.entry", "acceptance must select a Boolean output",
                acceptance.span);
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
