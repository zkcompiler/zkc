#ifndef ZKC_TRANSFORMS_LINEAR_CONTRACTION_H
#define ZKC_TRANSFORMS_LINEAR_CONTRACTION_H
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Interfaces/LinearContraction.h"
#include "llvm/ADT/SmallVector.h"

namespace zkc {
struct LinearContractionStats {
  unsigned producers = 0;
  unsigned eligiblePairs = 0;
  unsigned selectedPairs = 0;
  unsigned eligibleProducers = 0;
  unsigned selectedProducers = 0;
};
/// A deterministic summary, also available in builds with MLIR statistics
/// disabled.
void printLinearContractionStats(const LinearContractionStats &,
                                 llvm::raw_ostream &);
struct LinearContractionUse {
  mlir::Operation *consumer;
  DiagonalContractionSelection contraction;
};
struct LinearContractionGroup {
  mlir::Operation *producer;
  DiagonalProducerSelection production;
  llvm::SmallVector<LinearContractionUse> uses;
};
/// Read-only, same-function all-uses analysis. Groups are atomic. No operation
/// moves; unavailable interfaces, escaping values and unmatched domains retain
/// dense execution.
llvm::SmallVector<LinearContractionGroup>
findLinearContractions(mlir::func::FuncOp, LinearContractionStats &);
} // namespace zkc
#endif
