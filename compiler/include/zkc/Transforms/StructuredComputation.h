#ifndef ZKC_TRANSFORMS_STRUCTUREDCOMPUTATION_H
#define ZKC_TRANSFORMS_STRUCTUREDCOMPUTATION_H

#include "zkc/Analysis/StructuredComputation.h"

namespace zkc::mathematical {
/// Construct a private Func/Tensor/Linalg candidate from a closed scalar field
/// formula. Each input slot is retained even if unused. This producer is not
/// evidence that the candidate realizes that formula.
mlir::OwningOpRef<mlir::ModuleOp>
proposeStructuredComputation(mlir::Block &formula, llvm::ArrayRef<bool> rowwise,
                             StructuredResult result);

/// Apply upstream elementwise fusion and scalar-region CSE/DCE. Read a
/// candidate again afterwards, and after any subsequent mutation. No persisted
/// approval bit.
mlir::LogicalResult optimizeStructuredComputation(mlir::ModuleOp candidate);

} // namespace zkc::mathematical
#endif
