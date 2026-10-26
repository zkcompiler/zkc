#ifndef ZKC_TRANSFORMS_FINITEVERIFICATION_H
#define ZKC_TRANSFORMS_FINITEVERIFICATION_H

#include "ScopedFinite.h"
#include "zkc/Transforms/Finite.h"

namespace zkc::mathematical {
class ScopedCandidate;
}
namespace zkc::finite {
// Private allowances for the actual independent reader. Changing them never
// replaces the reader or grants admission. Each declaration starts a scope.
struct VerificationLimits {
  uint64_t reader = 100000;
  uint64_t comparison = 100000;
  // Optional containing-transaction balances. Required readers debit actual
  // consumption alongside their local caps, leaving unspent work for children.
  uint64_t *sharedReader = nullptr;
  // Comparisons reserve a bounded allowance and return only its unused part.
  uint64_t *sharedComparison = nullptr;
  uint64_t *sharedContext = nullptr;
  uint64_t *sharedSiteBytes = nullptr;
  // Borrowed actual scoped candidate; mutation invalidates the whole view.
  const mathematical::ScopedCandidate *candidate = nullptr;
  ScopedCallbackReader callback = {};
  // Required exact site sequence for ordered scoped preparation. Empty only
  // for readers whose enclosing numerical recipe checks occurrence names.
  llvm::StringRef finiteSite = {};
};
enum class VerificationStatus {
  Verified,
  Mismatch,
  OptionalCapacity,
  RequiredCapacity
};
struct VerificationResult {
  VerificationStatus status;
  llvm::StringRef detail;
  std::optional<CapacityCause> capacity = {};
  /// Copied before temporary normalization subjects can be destroyed.
  mathematical::RealizationSubject subject = {};

  // Used only when a result is final, after any optional-candidate retry.
  mlir::LogicalResult diagnose(mlir::ModuleOp candidate) const;
};

VerificationResult checkRealizations(mlir::ModuleOp original,
                                     mlir::ModuleOp candidate,
                                     VerificationLimits limits = {});

// Typed inline outcome for the containing checked transaction. This overload
// does not diagnose capacity; the transaction may discard an optional proposal.
// Disabled bulk policy requires the ordered payload after domain admission.
mlir::FailureOr<llvm::SmallVector<mlir::Value>> verifyExpression(
    mlir::Operation *source, mlir::ValueRange inputs, mlir::Operation *&cursor,
    HelperReader helper, mlir::Operation *symbolRoot, VerificationLimits limits,
    VerificationResult &outcome, MathematicalSelectionPolicy policy = {});

} // namespace zkc::finite
#endif
