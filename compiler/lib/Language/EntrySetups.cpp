#include "Internal.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Language/Layout.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
Error checkSetups(const ClosedEntry &entry, Layouts &layouts, Work &work) {
  const auto &protocol = entry.protocol();
  const auto &choices = entry.entry();
  std::set<unsigned> expected, covered;
  std::map<unsigned, unsigned> verifierKeys;
  unsigned offset = 0;
  for (unsigned port = 0; port < protocol.inputs.size(); ++port) {
    const auto &input = protocol.inputs[port];
    auto layout = layouts.get(input.type);
    if (!layout)
      return layout.takeError();
    for (const auto &leaf : (*layout)->leaves) {
      if (!leaf.data())
        return failure("source.entry", "Entry input requires executable data",
                       input.span);
      protocol::TypeParseBudget budget;
      budget.remaining =
          std::min<uint64_t>(budget.remaining, work.limits.work - work.used);
      auto before = budget.remaining;
      auto type = protocol::parseBoundType(*leaf.data(), false, 0, &budget);
      if (!type) {
        consumeError(type.takeError());
        return failure(budget.remaining ? "source.entry" : "source.limit",
                       "setup input type admission failed", input.span);
      }
      if (auto error =
              work.charge(before - budget.remaining + leaf.cost(), input.span))
        return error;
      if (choices.proof() && type->kind == "prover_key" &&
          llvm::is_contained(input.roles, choices.proof()->verifier))
        return failure("source.entry",
                       "proof prover keys must stay with the prover",
                       input.span);
      if (protocol::nativeSetupType(*type))
        expected.insert(offset);
      if (type->kind == "verifier_key") {
        if ((*layout)->type.kind != Type::Kind::Builtin ||
            (*layout)->leaves.size() != 1)
          return failure("source.ingress",
                         "key initialization requires a whole builtin port",
                         input.span);
        verifierKeys.emplace(offset, port);
      }
      ++offset;
    }
  }
  if (choices.proof() && verifierKeys.size() > 64)
    return failure("source.limit", "proof verifier key limit exceeded",
                   choices.span);
  for (const auto &slot : choices.setups) {
    bool publicVerifier = false;
    for (const auto &input : slot.inputs) {
      if (auto error = work.charge(input.path.size() + 1, input.span))
        return error;
      auto selected = layouts.selectInput(protocol, input);
      if (!selected)
        return selected.takeError();
      bool nonempty = false;
      for (unsigned i = 0; i < selected->layout->leaves.size(); ++i) {
        if (auto error = work.charge(1, input.span))
          return error;
        unsigned index = selected->offset + i;
        if (!expected.count(index))
          continue;
        nonempty = true;
        if (!covered.insert(index).second)
          return failure("source.entry", "setup selectors overlap", input.span);
        if (auto key = verifierKeys.find(index); key != verifierKeys.end()) {
          if (!choices.proof())
            continue;
          auto port = key->second;
          if (!llvm::is_contained(choices.proof()->publicInputs, port) ||
              !llvm::is_contained(protocol.inputs[port].roles,
                                  choices.proof()->verifier))
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
