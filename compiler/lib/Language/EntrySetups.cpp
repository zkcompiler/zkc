#include "Internal.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Language/EntryBoundary.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
Error checkSetups(const ClosedEntry &entry, Layouts &layouts, Work &work) {
  if (!entry.protocolOrNull())
    return Error::success();
  const auto &protocol = entry.protocol();
  const auto &choices = entry.entry();
  std::set<unsigned> expected, covered;
  struct VerifierKey {
    unsigned port;
    std::vector<unsigned> path, roles;
  };
  std::map<unsigned, VerifierKey> verifierKeys;
  std::vector<ProtocolPortLayout> ports;
  std::vector<unsigned> offsets;
  unsigned offset = 0;
  for (auto [ordinal, input] : enumerate(protocol.inputs)) {
    auto observed = layouts.protocolPort(input);
    if (!observed)
      return observed.takeError();
    offsets.push_back(offset);
    for (const auto &leaf : observed->leaves) {
      if (!leaf.leaf.data() || leaf.custody)
        continue;
      protocol::TypeParseBudget budget;
      budget.remaining =
          std::min<uint64_t>(budget.remaining, work.limits.work - work.used);
      auto before = budget.remaining;
      auto type =
          protocol::parseBoundType(*leaf.leaf.data(), false, 0, &budget);
      if (!type) {
        consumeError(type.takeError());
        return failure(budget.remaining ? "source.entry" : "source.limit",
                       "setup input type admission failed", input.span);
      }
      if (auto e = work.charge(before - budget.remaining + leaf.leaf.cost(),
                               input.span))
        return e;
      auto roles = leaf.roles();
      if (choices.proof() && type->kind == "prover_key" &&
          is_contained(roles, choices.proof()->verifier))
        return failure("source.entry",
                       "proof prover keys must stay with the prover",
                       input.span);
      unsigned index = offset + leaf.nativeOffset;
      if (protocol::nativeSetupType(*type))
        expected.insert(index);
      if (type->kind == "verifier_key") {
        auto selected = observed->body;
        for (auto step : leaf.path)
          selected = selected->fields[step].layout;
        if (selected->type.kind != Type::Kind::Builtin ||
            selected->leaves.size() != 1)
          return failure("source.ingress",
                         "key initialization requires an exact builtin field",
                         input.span);
        verifierKeys.emplace(index,
                             VerifierKey{unsigned(ordinal), leaf.path, roles});
      }
    }
    offset += observed->size();
    ports.push_back(std::move(*observed));
  }
  if (choices.proof() && verifierKeys.size() > 64)
    return failure("source.limit", "proof verifier key limit exceeded",
                   choices.span);
  for (const auto &slot : choices.setups) {
    bool publicVerifier = false;
    for (const auto &input : slot.inputs) {
      if (auto e = work.charge(input.path.size() + 1, input.span))
        return e;
      if (input.port >= ports.size())
        return failure("source.entry", "setup input is absent", input.span);
      const auto &port = ports[input.port];
      auto schema = port.body;
      for (auto step : input.path) {
        if (schema->custodyCount || schema->sealed ||
            schema->type.kind == Type::Kind::Associated ||
            schema->type.kind == Type::Kind::Variant ||
            step >= schema->fields.size() || !schema->fields[step].isPublic)
          return failure("source.entry",
                         "setup selector requires a visible product path",
                         input.span);
        schema = schema->fields[step].layout;
      }
      bool nonempty = false;
      for (const auto &leaf : port.leaves) {
        if (auto e = work.charge(leaf.path.size() + 1, input.span))
          return e;
        if (!entryPathContains(input.port, input.path, input.port, leaf.path))
          continue;
        unsigned index = offsets[input.port] + leaf.nativeOffset;
        if (!expected.count(index))
          continue;
        nonempty = true;
        if (!covered.insert(index).second)
          return failure("source.entry", "setup selectors overlap", input.span);
        if (auto key = verifierKeys.find(index);
            key != verifierKeys.end() && choices.proof()) {
          const auto &selected = key->second;
          bool isPublic = any_of(
              choices.proof()->publicInputs, [&](const EntryInputSelection &p) {
                return p.role == choices.proof()->verifier &&
                       entryPathContains(p.port, p.path, selected.port,
                                         selected.path);
              });
          if (!isPublic ||
              !is_contained(selected.roles, choices.proof()->verifier))
            return failure("source.entry",
                           "proof setup keys must be public verifier inputs",
                           input.span);
          publicVerifier = true;
        }
      }
      if (!nonempty)
        return failure("source.entry",
                       "setup selector contains no setup-bearing input",
                       input.span);
    }
    if (choices.proof() && !publicVerifier)
      return failure("source.entry",
                     "proof setup slot requires a public verifier key",
                     slot.span);
  }
  if (expected != covered)
    return failure("source.entry",
                   "setup-bearing inputs require exactly one setup slot",
                   choices.span);
  return Error::success();
}
} // namespace zkc::language::detail
