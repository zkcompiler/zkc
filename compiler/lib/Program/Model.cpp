#include "zkc/Program/Model.h"
#include <iterator>
#include <type_traits>

using namespace llvm;
namespace zkc::program {
StringRef Instruction::kind() const {
  static constexpr const char *names[] = {
      "op",      "local", "send",    "receive",       "return",    "yield",
      "stop",    "loop",  "release", "apply",         "if",        "for",
      "variant", "match", "query",   "bool_constant", "return_if", "if",
      "match"};
  static_assert(std::size(names) == std::variant_size_v<Value>);
  return names[value.index()];
}
bool Instruction::isTerminator() const {
  return get<Return>() || get<Yield>() || get<Stop>();
}

namespace {
template <typename B, typename F> void walkBody(B &body, F callback) {
  using I =
      std::conditional_t<std::is_const_v<B>, const Instruction, Instruction>;
  std::vector<I *> pending;
  for (auto it = body.rbegin(); it != body.rend(); ++it)
    pending.push_back(&*it);
  while (!pending.empty()) {
    auto *instruction = pending.back();
    pending.pop_back();
    callback(*instruction);
    auto push = [&](auto &nested) {
      for (auto it = nested.rbegin(); it != nested.rend(); ++it)
        pending.push_back(&*it);
    };
    auto arms = [&](auto *match) {
      if (match)
        for (auto it = match->arms.rbegin(); it != match->arms.rend(); ++it)
          push(it->body);
    };
    auto branches = [&](auto *branch) {
      if (branch) {
        push(branch->elseBody);
        push(branch->thenBody);
      }
    };
    arms(instruction->template get<Match>());
    arms(instruction->template get<ParticipantMatch>());
    if (auto *loop = instruction->template get<Loop>())
      push(loop->body);
    if (auto *loop = instruction->template get<For>())
      push(loop->body);
    branches(instruction->template get<Conditional>());
    branches(instruction->template get<ParticipantConditional>());
  }
}
} // namespace
void walk(const Body &body, function_ref<void(const Instruction &)> callback) {
  walkBody(body, callback);
}
void walk(Body &body, function_ref<void(Instruction &)> callback) {
  walkBody(body, callback);
}
} // namespace zkc::program
