#ifndef ZKC_TRANSFORMS_COLLECTFOLD_H
#define ZKC_TRANSFORMS_COLLECTFOLD_H
#include "FiniteVerification.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Transforms/Finite.h"
namespace zkc::finite {
// A borrowed structural view only. Neither selection nor transition evidence.
struct CollectFold {
  Computation producer, consumer;
  bool indexed = false;
  mlir::Value collected;
};
// Bounded discovery on admitted source IR. Exhaustion or unsupported uses
// decline the optional path.
mlir::FailureOr<CollectFold> readCollectFold(mlir::Operation *producer,
                                             mlir::Operation *consumer,
                                             uint64_t &remaining);
using ComposedHelperReader =
    llvm::function_ref<mlir::FailureOr<llvm::SmallVector<mlir::Value>>(
        mlir::Operation *, mlir::ValueRange, mlir::Operation *&,
        mlir::Value collected, mlir::Value position, mlir::Value element)>;
mlir::FailureOr<llvm::SmallVector<mlir::Value>>
realizeCollectFold(const CollectFold &, mlir::ValueRange producerInputs,
                   mlir::ValueRange consumerInputs, mlir::OpBuilder &,
                   mathematical::RealizationWork &);
mlir::FailureOr<llvm::SmallVector<mlir::Value>>
verifyCollectFold(const CollectFold &, mlir::ValueRange producerInputs,
                  mlir::ValueRange consumerInputs, mlir::Operation *&,
                  HelperReader, ComposedHelperReader, VerificationLimits,
                  VerificationResult &outcome);
} // namespace zkc::finite
#endif
