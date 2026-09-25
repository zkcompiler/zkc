#ifndef ZKC_PROTOCOL_ENCODINGLIMITS_H
#define ZKC_PROTOCOL_ENCODINGLIMITS_H

#include "zkc/Source/Model.h"
#include "zkc/Target/Json.h"

namespace zkc::protocol {
namespace detail {

// The admitted interactive carrier has a stricter array-depth bound than the
// authoring parser. Preserve it without materializing an encoded source tree.
// Top-level declaration bodies are arrays at depth 3 (root array is depth 0).
inline const source::Node *excessiveDepth(const source::Body &body,
                                          unsigned depth = 3) {
  for (const auto &instruction : body) {
    unsigned recordDepth = depth + 1;
    bool lists =
        instruction.get<source::Operation>() ||
        instruction.get<source::AlgorithmCall>() ||
        instruction.get<source::LocalCall>() ||
        instruction.get<source::ProtocolCall>() ||
        instruction.get<source::Return>() || instruction.get<source::Yield>() ||
        instruction.get<source::Release>() || instruction.get<source::Loop>() ||
        instruction.get<source::Conditional>() ||
        instruction.get<source::For>() ||
        instruction.get<source::VariantConstruct>() ||
        instruction.get<source::Match>();
    if (recordDepth >= 64 || (lists && recordDepth + 1 >= 64))
      return &instruction;
    if (auto *match = instruction.get<source::Match>()) {
      if (recordDepth + 3 >= 64)
        return &instruction;
      for (const auto &arm : match->arms)
        if (auto *failure = excessiveDepth(arm.body, recordDepth + 3))
          return failure;
    }
    if (auto *branch = instruction.get<source::Conditional>()) {
      if (auto *failure = excessiveDepth(branch->thenBody, recordDepth + 1))
        return failure;
      if (auto *failure = excessiveDepth(branch->elseBody, recordDepth + 1))
        return failure;
    }
    if (auto *loop = instruction.get<source::For>()) {
      if (!loop->carried.empty() && recordDepth + 2 >= 64)
        return &instruction;
      if (auto *failure = excessiveDepth(loop->body, recordDepth + 1))
        return failure;
    }
    if (auto *loop = instruction.get<source::Loop>()) {
      if (!loop->carried.empty() && recordDepth + 2 >= 64)
        return &instruction;
      if (auto *failure = excessiveDepth(loop->body, recordDepth + 1))
        return failure;
    }
  }
  return nullptr;
}

inline const source::Node *excessiveDepth(const source::Module &module) {
  for (const auto &function : module.functions)
    if (function.body)
      if (auto *failure = excessiveDepth(*function.body))
        return failure;
  for (const auto &protocol : module.protocols)
    if (protocol.body)
      if (auto *failure = excessiveDepth(*protocol.body))
        return failure;
  return nullptr;
}
inline const source::Node *excessiveDepth(const source::Participants &module) {
  for (const auto &function : module.functions)
    if (function.body)
      if (auto *failure = excessiveDepth(*function.body))
        return failure;
  for (const auto &participant : module.participants)
    if (auto *failure = excessiveDepth(participant.body))
      return failure;
  return nullptr;
}
} // namespace detail
} // namespace zkc::protocol
#endif
