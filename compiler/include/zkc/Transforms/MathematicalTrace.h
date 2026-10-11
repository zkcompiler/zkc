#ifndef ZKC_TRANSFORMS_MATHEMATICALTRACE_H
#define ZKC_TRANSFORMS_MATHEMATICALTRACE_H

#include "zkc/Transforms/MathematicalSelection.h"
#include "zkc/Transforms/MathematicalWork.h"
#include <cstdint>
#include <string>
#include <vector>

namespace llvm {
class raw_ostream;
}
namespace zkc::mathematical {
/// Diagnostic measurements for one invocation, never admission evidence. A
/// completed stage may make no change. Counts include declarations and nested
/// regions; duration includes the stage's own formation and relation checks.
struct RealizationStage {
  std::string name;
  bool completed = false;
  uint64_t operationsBefore = 0, operationsAfter = 0;
  uint64_t microseconds = 0;
};
struct RealizationTrace {
  /// Effective choices used by the recorded invocation.
  MathematicalSelectionPolicy policy;
  std::vector<RealizationStage> stages;
  RealizationWork initialWork, remainingWork;
  bool remarks = false;
  /// Optional diagnostic before/after IR. Failed proposals are never exported
  /// as checked programs; dumps identify their stage and completion status.
  /// The caller owns this stream throughout the synchronous invocation.
  llvm::raw_ostream *ir = nullptr;
};
} // namespace zkc::mathematical
#endif
