#include "zkc/Source/Model.h"
#include <type_traits>

using namespace llvm;
namespace zkc::source {
StringRef Instruction::kind() const {
  static constexpr const char *names[] = {
      "op",     "local", "call", "message",    "send", "receive",
      "return", "yield", "stop", "incomplete", "loop", "release",
      "apply",  "if",    "for",  "variant",    "match"};
  return names[value.index()];
}
bool Instruction::isTerminator() const {
  return get<Return>() || get<Yield>() || get<Stop>() || get<Incomplete>();
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
template <typename C, typename F> void walkContent(C &content, F callback) {
  auto local = [&](auto &function) {
    callback(function);
    if (function.body)
      walkBody(*function.body, callback);
  };
  std::visit(
      [&](auto &root) {
        using T = std::decay_t<decltype(root)>;
        callback(root);
        if constexpr (std::is_same_v<T, Construction>) {
          for (auto &binding : root.publicBindings)
            callback(binding);
        } else {
          for (auto &binding : root.bindings)
            callback(binding);
          for (auto &function : root.functions)
            local(function);
          if constexpr (std::is_same_v<T, Module>) {
            for (auto &relation : root.relations)
              callback(relation);
            for (auto &view : root.relationViews)
              callback(view);
            for (auto &protocol : root.protocols) {
              callback(protocol);
              for (auto &dependency : protocol.dependencies)
                callback(dependency);
              if (protocol.body)
                walkBody(*protocol.body, callback);
            }
            for (auto &instance : root.instances)
              callback(instance);
            for (auto &definition : root.definitions) {
              callback(definition);
              for (auto &requirement : definition.requirements)
                callback(requirement);
              walkBody(definition.body, callback);
            }
            for (auto &configuration : root.configurations)
              callback(configuration);
          } else {
            for (auto &participant : root.participants) {
              callback(participant);
              walkBody(participant.body, callback);
            }
          }
          for (auto &entry : root.entries)
            callback(entry);
        }
      },
      content);
}
} // namespace
void walk(const Content &content, function_ref<void(const Node &)> callback) {
  walkContent(content, callback);
}
void walk(Content &content, function_ref<void(Node &)> callback) {
  walkContent(content, callback);
}
void walk(const Body &body, function_ref<void(const Instruction &)> callback) {
  walkBody(body, callback);
}
void walk(Body &body, function_ref<void(Instruction &)> callback) {
  walkBody(body, callback);
}
} // namespace zkc::source
