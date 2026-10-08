#include "zkc/Program/Model.h"
#include <type_traits>

using namespace llvm;
namespace zkc::program {
StringRef Instruction::kind() const {
  static constexpr const char *names[] = {
      "op",      "local", "send",    "receive",       "return",   "yield",
      "stop",    "loop",  "release", "apply",         "if",       "for",
      "variant", "match", "query",   "bool_constant", "return_if"};
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
    if (auto *match = instruction->template get<Match>())
      for (auto it = match->arms.rbegin(); it != match->arms.rend(); ++it)
        push(it->body);
    if (auto *loop = instruction->template get<Loop>())
      push(loop->body);
    if (auto *loop = instruction->template get<For>())
      push(loop->body);
    if (auto *branch = instruction->template get<Conditional>()) {
      push(branch->elseBody);
      push(branch->thenBody);
    }
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
