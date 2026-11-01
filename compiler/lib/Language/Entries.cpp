#include "Checker.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Language/Builtins.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
bool Checker::entry(DeclarationId id, unsigned depth) {
  auto &state = entryStates;
  auto &entry = output.declarations[id.index];
  // Zero is unseen, one is active, and completed states retain 1 + height.
  // Cached aliases must still satisfy the caller's remaining depth budget.
  if (state[id.index] >= 2)
    return uint64_t(depth) - 1 + state[id.index] - 1 <= work.limits.callDepth ||
           types.fail("source.limit", "Entry alias depth exceeded", entry.span);
  if (state[id.index] == 1)
    return types.fail("source.entry", "complete Entry aliases must be acyclic",
                      entry.span);
  if (depth > work.limits.callDepth || !types.charge(1, entry.span))
    return types.diagnostic
               ? false
               : types.fail("source.limit", "Entry alias depth exceeded",
                            entry.span);
  state[id.index] = 1;
  unsigned height = 1;
  const auto &source = *sources[id.index];
  auto target = resolve(entry, source.target, source.span);
  if (!target)
    return false;
  if (!signature(*target))
    return false;
  const auto &definition = output.declarations[target->index];
  if (definition.kind == Declaration::Kind::Entry) {
    if (source.entryBlock || !source.targetArguments.empty())
      return types.fail(
          "source.entry",
          "complete Entry aliases cannot override or specialize choices",
          source.span);
    if (!this->entry(*target, depth + 1))
      return false;
    if (source.entryKind != definition.entryKind())
      return types.fail("source.entry",
                        "Entry aliases must have the same run/proof kind",
                        source.span);
    uint64_t copied = definition.staticArguments.size();
    if (definition.proof()) {
      for (const auto &gate : definition.proof()->gates)
        for (const auto &part : gate.path)
          if (!types.charge(part.size() + 1, source.span))
            return false;
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

    height = state[target->index];
    entry.target = definition.target;
    entry.staticArguments = definition.staticArguments;
    entry.configuration = definition.configuration;
    for (const auto &slot : definition.setups) {
      if (!types.charge(slot.name.size() + slot.inputs.size() + 1, source.span))
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

    entry.target = *target;
    entry.staticArguments = std::move(*selected);
    if (source.proof && source.proof->selectedConstruction && !constructions())
      return false;
    if (source.proof && !body(*target, 1))
      return false;
    if (source.proof && !configureEntry(entry, definition, *source.proof))
      return false;
    if (source.setups.empty())
      entry.setups = definition.setups;
    if (!configureSetups(entry, definition, source.setups))
      return false;
  } else
    return types.fail("source.entry",
                      "entry target must be a protocol or complete Entry",
                      source.span);
  if (uint64_t(depth) - 1 + height > work.limits.callDepth)
    return types.fail("source.limit", "Entry alias depth exceeded", entry.span);
  state[id.index] = height + 1;
  return true;
}
bool Checker::entries() {
  for (unsigned i = 0; i < sources.size(); ++i)
    if (output.declarations[i].kind == Declaration::Kind::Entry && !entry({i}))
      return false;
  return true;
}
bool Checker::configureSetups(Declaration &entry, const Declaration &protocol,
                              ArrayRef<SyntaxSetupSlot> sources) {
  if (sources.size() > 64)
    return types.fail("source.limit", "Entry setup slot limit exceeded",
                      entry.span);
  auto bindings = entry.kind == Declaration::Kind::Protocol
                      ? Substitution{}
                      : types.substitution(protocol, entry.staticArguments);
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
      InputSelector selected{
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
  if (source.selectedConstruction) {
    const auto &choice = *source.selectedConstruction;
    auto selected = resolve(entry, choice.name, choice.span);
    if (!selected)
      return false;
    const auto &definition = output.declarations[selected->index];
    if (definition.kind != Declaration::Kind::Construction ||
        !definition.target || definition.target->index != protocol.id.index)
      return types.fail("source.construction",
                        "construction targets another protocol", choice.span);
    auto actual = arguments(entry, definition, choice.arguments, choice.span,
                            choice.labels);
    if (!actual)
      return false;
    auto bindings = types.substitution(definition, *actual);
    std::vector<Type> targetArguments;
    for (const auto &argument : definition.staticArguments) {
      auto closed = types.substitute(argument, bindings, choice.span);
      if (!closed)
        return false;
      targetArguments.push_back(std::move(*closed));
    }
    if (targetArguments != entry.staticArguments)
      return types.fail("source.construction",
                        "construction specialization differs from Entry",
                        choice.span);
    value.format =
        definition.proofFormat.value_or(protocol::ProofFormat::Native);
    value.selectedConstruction = *selected;
    value.constructionArguments = std::move(*actual);
    const auto &construction = *definition.construction;
    value.services = construction.services;
    value.suite = construction.suite;
    value.construction = construction.provider || !construction.rules.empty()
                             ? ProofEntry::Construction::Derived
                         : construction.suite.empty()
                             ? ProofEntry::Construction::Authored
                             : ProofEntry::Construction::FiatShamir;
  }
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
    auto service = portIndex(protocol.services, *source.service);
    if (!service)
      return false;
    value.services = {*service};
  }
  value.gates = source.gates;
  auto order = types.proofGateOrder(protocol, value);
  if (!order)
    return false;
  auto gates = std::move(value.gates);
  value.gates.clear();
  for (unsigned index : *order)
    value.gates.push_back(std::move(gates[index]));
  entry.configuration = std::move(value);
  return types.checkProofEntry(entry, protocol);
}

} // namespace zkc::language::detail

namespace zkc::language::detail {
/// Generated declarations use the same nominal representation and substitution
/// as authored data. They are allocated during collection, before signatures
/// can retain references into the declaration table.
bool Checker::generatedSignature(Declaration &decl, unsigned depth) {
  auto id = decl.id;
  if (signatureState[id.index] == 2)
    return true;
  if (signatureState[id.index] == 1)
    return types.fail("source.cycle", "recursive generated signature",
                      decl.span);
  if (depth > work.limits.typeDepth || !types.charge(1, decl.span))
    return types.diagnostic
               ? false
               : types.fail("source.limit", "generated signature depth",
                            decl.span);
  signatureState[id.index] = 1;
  const auto target = decl.generated->target;
  if (!signature(target, depth + 1))
    return false;
  auto &owner = output.declarations[target.index];
  bool proof = owner.kind == Declaration::Kind::Entry;
  if (proof && !entry(target))
    return false;
  const auto &protocol =
      proof ? output.declarations[owner.target->index] : owner;
  const auto &member = decl.generated->member;
  if (!chargeStaticSignature(owner))
    return false;
  decl.parameters = owner.parameters;
  decl.bounds = owner.bounds;
  decl.capabilityBounds = owner.capabilityBounds;
  decl.permissionBounds = owner.permissionBounds;
  auto subst = proof ? types.substitution(protocol, owner.staticArguments)
                     : Substitution{};
  auto nominal = [&](DeclarationId definition) {
    const auto &d = output.declarations[definition.index];
    Type type(d.kind == Declaration::Kind::Variant ? Type::Kind::Variant
                                                   : Type::Kind::Record,
              d.qualifiedName);
    for (const auto &p : owner.parameters)
      type.arguments.push_back(parameterType(p));
    return type;
  };
  auto sibling = [&](StringRef name) -> std::optional<DeclarationId> {
    for (auto child : owner.members)
      if (output.declarations[child.index].name == name) {
        if (!signature(child, depth + 1))
          return {};
        return child;
      }
    types.fail("source.host-api", "missing generated member", decl.span);
    return {};
  };
  auto addMember = [&](StringRef label, StringRef name) {
    auto child = sibling(name);
    if (!child || !types.chargeType(nominal(*child), decl.span))
      return false;
    decl.fields.push_back({label.str(), nominal(*child), true, decl.span});
    return true;
  };
  // Setup and managed authority are never ordinary input constructors. A
  // setup-bearing logical port is supplied by the Host operation context.
  auto ports = [&](bool inputs, std::optional<unsigned> role, bool publicOnly,
                   bool witness) {
    decl.generated->role = role;
    const auto &ports = inputs ? protocol.inputs : protocol.outputs;
    for (unsigned i = 0; i < ports.size(); ++i) {
      const auto &port = ports[i];
      if (!types.charge(port.roles.size() + 1, port.span))
        return false;
      if (role && !llvm::is_contained(port.roles, *role))
        continue;
      bool isPublic =
          proof && llvm::is_contained(owner.proof()->publicInputs, i);
      if (inputs && ((publicOnly && !isPublic) || (witness && isPublic)))
        continue;
      auto type = types.substitute(port.type, subst, port.span);
      if (!type)
        return false;
      if (inputs) {
        bool setup = llvm::any_of(owner.setups, [&](const SetupSlot &slot) {
          return llvm::any_of(slot.inputs, [&](const InputSelector &selector) {
            return selector.port == i;
          });
        });
        auto authority = types.setupAuthority(*type, port.span);
        if (!authority)
          return false;
        if (setup || *authority)
          continue;
      }
      if (!types.chargeType(*type, port.span))
        return false;
      decl.generated->ports.push_back({i, {}, port.span});
      decl.fields.push_back({port.name, std::move(*type), true, port.span});
    }
    return true;
  };
  decl.generated->constructible = member == "Inputs" || member == "Public" ||
                                  member == "Witness" || member == "Proof" ||
                                  StringRef(member).starts_with("Inputs:");
  if (member == "run" || member == "prove" || member == "verify") {
    decl.generated->operation = member == "run" ? HostInvocation::Kind::Run
                                : member == "prove"
                                    ? HostInvocation::Kind::Prove
                                    : HostInvocation::Kind::Verify;
    auto input = [&](StringRef label, StringRef name) {
      auto child = sibling(name);
      if (!child)
        return false;
      decl.inputOrder.push_back(
          {Declaration::InputSlot::Kind::Data, unsigned(decl.inputs.size())});
      decl.inputs.push_back({label.str(), nominal(*child), {}, decl.span});
      return true;
    };
    if (member == "run" ? !input("inputs", "Inputs")
                        : (!input("public", "Public") ||
                           !input(member == "prove" ? "witness" : "proof",
                                  member == "prove" ? "Witness" : "Proof")))
      return false;
    auto result = sibling(member == "run"     ? "RunResult"
                          : member == "prove" ? "ProveResult"
                                              : "VerifyResult");
    if (!result)
      return false;
    decl.outputs.push_back({"result", nominal(*result), {}, decl.span});
    decl.effectAllowance = EffectSummary{Effects{true, false}};
    if (member == "run") {
      if (!types.charge(4 + decl.parameters.size(), decl.span))
        return false;
      Body body;
      body.mode = Body::Mode::Local;
      body.stage = Body::Stage::Host;
      body.inputs = 1;
      body.values = {{decl.inputs.front().type, {}, decl.span},
                     {decl.outputs.front().type, {}, decl.span}};
      std::vector<Type> arguments;
      for (const auto &parameter : decl.parameters)
        arguments.push_back(parameterType(parameter));
      body.operations.push_back({HostInvocation{HostInvocation::Kind::Run,
                                                target,
                                                std::move(arguments),
                                                {ValueId{0}}},
                                 {ValueId{1}},
                                 decl.span,
                                 0});
      body.results = {ValueId{1}};
      body.effects.fixed.mayStop = true;
      decl.body = std::make_shared<Body>(std::move(body));
    }
  } else if (member == "Inputs" || member == "RunResult") {
    for (auto child : decl.members) {
      if (!signature(child, depth + 1))
        return false;
      decl.fields.push_back({output.declarations[child.index].name,
                             nominal(child), true, decl.span});
    }
  } else if (StringRef(member).contains(':')) {
    auto parts = StringRef(member).split(':');
    auto found = llvm::find(protocol.roles, parts.second);
    if (found == protocol.roles.end() ||
        !ports(parts.first == "Inputs",
               unsigned(found - protocol.roles.begin()), false, false))
      return false;
  } else if (member == "Public") {
    if (!ports(true, {}, true, false))
      return false;
  } else if (member == "Witness") {
    if (!ports(true, owner.proof()->prover, false, true))
      return false;
  } else if (member == "Proof") {
    auto bytes = builtinType("bytes", {});
    if (!bytes)
      return types.accept(bytes.takeError(), decl.span);
    decl.fields.push_back({"bytes", *bytes, true, decl.span});
  } else if (member == "ProverOutputs" || member == "VerifierOutputs") {
    if (!ports(false,
               member == "ProverOutputs" ? owner.proof()->prover
                                         : owner.proof()->verifier,
               false, false))
      return false;
  } else if (member == "ProveResult") {
    if (!addMember("proof", "Proof") || !addMember("outputs", "ProverOutputs"))
      return false;
  } else if (member == "VerifyResult") {
    auto outputs = sibling("VerifierOutputs");
    if (!outputs)
      return false;
    decl.alternatives = {{"Accepted",
                          {{"outputs", nominal(*outputs), true, decl.span}},
                          decl.span},
                         {"Rejected", {}, decl.span}};
  } else
    return types.fail("source.host-api", "unknown generated API member",
                      decl.span);
  if (!types.charge(decl.inputs.size() + decl.outputs.size() +
                        decl.fields.size() + decl.alternatives.size() + 1,
                    decl.span))
    return false;
  signatureState[id.index] = 2;
  return true;
}
} // namespace zkc::language::detail
