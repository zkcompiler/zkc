#ifndef ZKC_TRANSFORMS_FINITEVERIFICATION_H
#define ZKC_TRANSFORMS_FINITEVERIFICATION_H

#include "zkc/Transforms/Finite.h"

namespace zkc::finite {
// Private allowances for the actual independent reader. Changing them never
// replaces the reader or grants admission. Each declaration starts a scope.
struct VerificationLimits {
  uint64_t reader = 100000;
  uint64_t comparison = 100000;
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

  // Used only when a result is final, after any optional-candidate retry.
  mlir::LogicalResult diagnose(mlir::ModuleOp candidate) const;
};

VerificationResult checkRealizations(mlir::ModuleOp original,
                                     mlir::ModuleOp candidate,
                                     VerificationLimits limits = {});

// Typed inline outcome for the containing checked transaction. This overload
// does not diagnose capacity; the transaction may discard an optional proposal.
mlir::FailureOr<llvm::SmallVector<mlir::Value>>
verifyExpression(mlir::Operation *source, mlir::ValueRange inputs,
                 mlir::Operation *&cursor, HelperReader helper,
                 mlir::Operation *symbolRoot, VerificationLimits limits,
                 VerificationResult &outcome);

} // namespace zkc::finite
#endif
