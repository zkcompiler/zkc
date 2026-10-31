#ifndef ZKC_ANALYSIS_SUCCESSFULCONTINUATIONS_H
#define ZKC_ANALYSIS_SUCCESSFULCONTINUATIONS_H

#include "mlir/IR/Operation.h"
#include "mlir/Pass/AnalysisManager.h"
#include "zkc/Contracts/MathematicalFacts.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include <memory>

namespace zkc {
/// Participant-relative unsigned bounds before an actual admitted Protocol
/// action. Admission of the complete immutable module is a caller prerequisite;
/// shared interaction extraction is structural, not an admission certificate.
/// Only containing/enclosing repeat prefixes supply guards. Calls are opaque,
/// repeats stay symbolic, and body facts never escape their current iteration.
class SuccessfulContinuationAnalysis {
public:
  enum class Status { Proven, Unknown, Unreachable, Capacity };
  struct Limits {
    unsigned depth = 64;
    unsigned actions = 100000;
  };
  explicit SuccessfulContinuationAnalysis(mlir::Operation *module);
  SuccessfulContinuationAnalysis(mlir::Operation *module, Limits);
  SuccessfulContinuationAnalysis(mlir::Operation *module,
                                 mlir::AnalysisManager &);
  ~SuccessfulContinuationAnalysis();
  SuccessfulContinuationAnalysis(const SuccessfulContinuationAnalysis &) =
      delete;
  SuccessfulContinuationAnalysis &
  operator=(const SuccessfulContinuationAnalysis &) = delete;
  bool isInvalidated(const mlir::AnalysisManager::PreservedAnalyses &);
  mlir::Operation *getOwner() const;

  /// Clear BEFORE mutating the subject, inspected helpers, roles, layouts,
  /// installations or policies. End-of-pass invalidation alone is insufficient.
  /// The module must outlive this analysis; reconstruct if the owner changes.
  /// Source/candidate modules (including clones) need separate instances.
  void clear();

  /// All queried SSA values and point must belong to this exact declaration
  /// and module. Only exact role restrictions and invariant repeat captures
  /// forward identity; carried initializers and callee formals do not.
  /// Every extraction, navigation, forwarding and lookup debits caller Work,
  /// including cache hits. Depth/structure exhaustion is sticky Capacity.
  /// Unknown and Unreachable never establish the requested bound. Structural
  /// refusals use Expected errors; no operations or guards are changed.
  llvm::Expected<Status> bound(mlir::Operation *declaration,
                               mlir::Operation *point,
                               llvm::StringRef participant, mlir::Value index,
                               mlir::Value upper, facts::Work &);
  /// A guarded exact integer RHS may weaken to this larger constant upper.
  llvm::Expected<Status> bound(mlir::Operation *declaration,
                               mlir::Operation *point,
                               llvm::StringRef participant, mlir::Value index,
                               uint64_t upper, facts::Work &);

private:
  struct Impl;
  std::unique_ptr<Impl> impl_;
};
} // namespace zkc
#endif
