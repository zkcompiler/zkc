#ifndef ZKC_LANGUAGE_FORMATIONCURSOR_H
#define ZKC_LANGUAGE_FORMATIONCURSOR_H
#include "DescriptorClosure.h"
namespace zkc::language::detail {
/// Read immutable occurrence blocks in invocation order. Payload sharing does
/// not suppress an invocation, and container length is independent of source
/// expression/call depth. Visitors never mutate this arena.
class FormationCursor {
  Semantics &types;
  const DescriptorArena &arena;

public:
  FormationCursor(Semantics &types, const DescriptorArena &arena)
      : types(types), arena(arena) {}
  bool walk(unsigned root,
            llvm::function_ref<bool(const DescriptorOccurrence &)> visit,
            bool occurrences = true) const {
    struct Frame {
      unsigned block, position;
    };
    std::vector<Frame> pending;
    std::set<unsigned> active;
    std::set<unsigned> completed;
    auto enter = [&](unsigned block) {
      if (occurrences ? pending.size() >= types.work.limits.callDepth
                      : pending.size() > types.work.limits.callDepth)
        return types.fail("source.limit", "formation invocation depth exceeded",
                          {});
      if (!types.charge(sizeof(Frame) +
                            2 * (sizeof(unsigned) + 4 * sizeof(void *)),
                        {}) ||
          block >= arena.blocks.size() || !active.insert(block).second)
        return types.diagnostic
                   ? false
                   : types.fail("source.domain-witness",
                                "invalid or cyclic formation invocation", {});
      if (!occurrences && completed.count(block)) {
        active.erase(block);
        return true;
      }
      pending.push_back({block, 0});
      return true;
    };
    if (!enter(root))
      return false;
    while (!pending.empty()) {
      auto &frame = pending.back();
      const auto &block = arena.blocks[frame.block];
      if (frame.position == block.size()) {
        completed.insert(frame.block);
        active.erase(frame.block);
        pending.pop_back();
        continue;
      }
      if (!types.charge(1, {}))
        return false;
      const auto &occurrence = block[frame.position++];
      if (occurrence.result >= arena.payloads.size())
        return types.fail("source.domain-witness",
                          "invalid formation occurrence", {});
      // Analysis may suspend while a value dependency is being extracted.
      // That is not malformed source or a failed admission judgment.
      if (!visit(occurrence))
        return false;
      if (occurrence.invocation && !enter(*occurrence.invocation))
        return false;
    }
    return true;
  }
};
template <class Result> struct FormationRead {
  Result selected;
  std::vector<Result> retained;
};
/// Analyses consume one common formation relation. The input reader preserves
/// its owning coordinate system: source analyses map ports to their Body's SSA
/// values, while closed analyses inspect the immutable shape's input slots.
/// Structural schemes and invocation frames are expanded only by formation.
template <class Result, class Input>
std::optional<FormationRead<Result>> readFormation(
    Semantics &types, const DescriptorShape &shape,
    llvm::function_ref<std::optional<Input>(unsigned, Span)> input,
    llvm::function_ref<Result(std::optional<unsigned>,
                              const DescriptorContract &)>
        parameter,
    llvm::function_ref<std::optional<Result>(const DescriptorBinding &,
                                             llvm::ArrayRef<Input>,
                                             llvm::ArrayRef<Result>)>
        leaf,
    llvm::function_ref<std::optional<Result>(
        DescriptorBinding::Kind, const DescriptorContract &,
        llvm::ArrayRef<Type>, llvm::ArrayRef<Result>)>
        compose) {
  if (!shape.arena)
    return {};
  const auto &arena = *shape.arena;
  if (!types.charge((arena.leaves.size() + arena.payloads.size()) *
                        sizeof(std::optional<Result>),
                    {}))
    return {};
  std::vector<std::optional<Result>> leaves(arena.leaves.size());
  std::vector<std::optional<Result>> values(arena.payloads.size());
  std::vector<Result> retained;
  auto visit = [&](const DescriptorOccurrence &event) {
    if (event.invocation || values[event.result])
      return true;
    const auto &payload = arena.payloads[event.result];
    const DescriptorBinding *operation = nullptr;
    std::vector<unsigned> children;
    if (auto *id = std::get_if<unsigned>(&payload.value)) {
      if (*id >= arena.leaves.size())
        return types.fail("source.descriptor",
                          "formation leaf is outside its arena", {});
      operation = &arena.leaves[*id];
      if (event.kind != operation->kind)
        return true; // A forward reuses its already visited constructor.
      if (!types.charge(operation->children.size() * sizeof(Result),
                        operation->span))
        return false;
    } else if (auto *open = std::get_if<DescriptorResidual>(&payload.value)) {
      if (!open->operation) {
        values[event.result] = parameter(open->parameter, payload.contract);
        return true;
      }
      operation = &*open->operation;
      if (!types.charge(open->children.size() * sizeof(unsigned),
                        operation->span))
        return false;
      children = open->children;
    } else {
      // The actual construction edges preserve sharing. Enumerating every
      // persistent sequence version would flatten shared histories repeatedly.
      if (!types.charge(event.children.size() * sizeof(unsigned), {}))
        return false;
      children = event.children;
    }
    if (!types.charge(
            (children.size() + (operation ? operation->children.size() : 0)) *
                    sizeof(Result) +
                sizeof(Result),
            {}))
      return false;
    std::vector<Result> arguments;
    arguments.reserve(children.size() +
                      (operation ? operation->children.size() : 0));
    for (auto child : children) {
      if (child >= values.size() || !values[child])
        return types.fail("source.descriptor", "formation precedes its child",
                          {});
      arguments.push_back(*values[child]);
    }
    if (operation && std::holds_alternative<unsigned>(payload.value))
      for (const auto &child : operation->children) {
        if (child.node >= leaves.size() || !leaves[child.node])
          return types.fail("source.descriptor",
                            "formation leaf precedes its child",
                            operation->span);
        arguments.push_back(*leaves[child.node]);
      }
    std::optional<Result> result;
    if (operation) {
      if (!types.charge(operation->operands.size() * sizeof(Input),
                        operation->span))
        return false;
      std::vector<Input> data;
      data.reserve(operation->operands.size());
      for (auto port : operation->operands) {
        if (port.index >= shape.inputs.size())
          return types.fail("source.descriptor",
                            "formation data selector differs", operation->span);
        auto actual = input(port.index, operation->span);
        if (!actual)
          return false;
        data.push_back(*actual);
      }
      result = leaf(*operation, data, arguments);
    } else
      result =
          compose(event.kind, payload.contract, payload.arguments, arguments);
    // Analysis can suspend until an SSA dependency has been extracted.
    if (!result || !types.charge(2 * sizeof(Result), {}))
      return false;
    if (operation)
      retained.push_back(*result);
    if (auto *id = std::get_if<unsigned>(&payload.value))
      leaves[*id] = *result;
    values[event.result] = std::move(*result);
    return true;
  };
  if (!FormationCursor(types, arena).walk(shape.formation, visit, false) ||
      shape.payload >= values.size() || !values[shape.payload])
    return {};
  return FormationRead<Result>{*values[shape.payload], std::move(retained)};
}
template <class Result>
std::optional<FormationRead<Result>> readFormation(
    Semantics &types, const DescriptorEnvironment &formation,
    llvm::function_ref<Result(std::optional<unsigned>,
                              const DescriptorContract &)>
        parameter,
    llvm::function_ref<std::optional<Result>(const DescriptorBinding &,
                                             llvm::ArrayRef<ValueId>,
                                             llvm::ArrayRef<Result>)>
        leaf,
    llvm::function_ref<std::optional<Result>(
        DescriptorBinding::Kind, const DescriptorContract &,
        llvm::ArrayRef<Type>, llvm::ArrayRef<Result>)>
        compose) {
  if (!formation.shape)
    return {};
  return readFormation<Result, ValueId>(
      types, *formation.shape,
      [&](unsigned port, Span span) -> std::optional<ValueId> {
        if (port >= formation.operands.size()) {
          types.fail("source.descriptor", "formation data selector differs",
                     span);
          return {};
        }
        return formation.operands[port];
      },
      parameter, leaf, compose);
}
} // namespace zkc::language::detail
#endif
