#ifndef ZKC_PROGRAM_ENCODINGLIMITS_H
#define ZKC_PROGRAM_ENCODINGLIMITS_H

#include "zkc/Program/Model.h"
#include "zkc/Support/Json.h"

namespace zkc::protocol {
namespace detail {
// The admitted interactive carrier has a stricter array-depth bound than the
// MLIR parser. Preserve it without materializing an encoded carrier.
// Top-level declaration bodies are arrays at depth 3 (root array is depth 0).
inline bool excessiveDepth(const program::Body &body, unsigned depth = 3) {
  for (const auto &instruction : body) {
    unsigned recordDepth = depth + 1;
    bool lists = instruction.get<program::Operation>() ||
                 instruction.get<program::LocalApply>() ||
                 instruction.get<program::LocalCall>() ||
                 instruction.get<program::Return>() ||
                 instruction.get<program::Yield>() ||
                 instruction.get<program::Release>() ||
                 instruction.get<program::Loop>() ||
                 instruction.get<program::Conditional>() ||
                 instruction.get<program::For>() ||
                 instruction.get<program::VariantConstruct>() ||
                 instruction.get<program::Match>();
    if (recordDepth >= 64 || (lists && recordDepth + 1 >= 64))
      return true;
    if (auto *match = instruction.get<program::Match>()) {
      if (recordDepth + 3 >= 64)
        return true;
      for (const auto &arm : match->arms)
        if (excessiveDepth(arm.body, recordDepth + 3))
          return true;
    }
    if (auto *branch = instruction.get<program::Conditional>()) {
      if (excessiveDepth(branch->thenBody, recordDepth + 1))
        return true;
      if (excessiveDepth(branch->elseBody, recordDepth + 1))
        return true;
    }
    if (auto *loop = instruction.get<program::For>()) {
      if (!loop->carried.empty() && recordDepth + 2 >= 64)
        return true;
      if (excessiveDepth(loop->body, recordDepth + 1))
        return true;
    }
    if (auto *loop = instruction.get<program::Loop>()) {
      if (!loop->carried.empty() && recordDepth + 2 >= 64)
        return true;
      if (excessiveDepth(loop->body, recordDepth + 1))
        return true;
    }
  }
  return false;
}

inline bool excessiveDepth(const program::LocalDefinitions &module) {
  for (const auto &function : module.functions)
    if (excessiveDepth(function.body))
      return true;
  return false;
}
inline bool excessiveDepth(const program::Participants &module) {
  for (const auto &function : module.functions)
    if (excessiveDepth(function.body))
      return true;
  for (const auto &participant : module.participants)
    if (excessiveDepth(participant.body))
      return true;
  return false;
}
} // namespace detail
} // namespace zkc::protocol
#endif
