#ifndef ZKC_TRANSFORMS_KERNEL_NORMALIZATIONVERIFICATION_H
#define ZKC_TRANSFORMS_KERNEL_NORMALIZATIONVERIFICATION_H

#include "zkc/Dialect/Operations.h"
#include "llvm/ADT/SmallVector.h"
#include <cstddef>
#include <memory>

namespace zkc::kernel {
// Independent, bounded readers of actual temporary MLIR. Source closures must
// already be admitted and remain immutable. Locations may change; attributes,
// concrete occurrences, SSA identities, result coordinates and cuts may not.
// Neither reader emits IR, invokes a producer, or trusts occurrence labels.
class NormalizationProvenanceChecker {
  struct Implementation;
  std::unique_ptr<Implementation> implementation;

public:
  explicit NormalizationProvenanceChecker(mlir::Operation *sourceRoot,
                                          size_t work = 4000000);
  ~NormalizationProvenanceChecker();

  // Exact static projection/dimension folds and dead total arithmetic only.
  // Live concrete instructions remain distinct, ordered and unchanged.
  mlir::LogicalResult checkSimplification(mlir::func::FuncOp source,
                                          mlir::Block &candidate);

  mlir::LogicalResult checkExpansion(mlir::func::FuncOp source,
                                     mlir::Block &expanded);

  // Expanded source has no func.call. Consume concrete instructions exactly,
  // and polynomial-generated instructions using the supported defining laws,
  // including their bounded caches. Retain the independent polynomial meaning
  // check as well. No concrete folding, CSE, DCE or frontier movement is
  // allowed. On success only, append independently read polynomial-generated
  // identities to generated. These handles belong to candidate and are
  // invalidated by edits.
  mlir::LogicalResult checkNormalization(
      mlir::func::FuncOp expanded, mlir::Block &candidate,
      llvm::SmallVectorImpl<mlir::Operation *> *generated = nullptr);
};
} // namespace zkc::kernel
#endif
