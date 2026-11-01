#ifndef ZKC_TRANSFORMS_RESIDUE_H
#define ZKC_TRANSFORMS_RESIDUE_H
#include "mlir/IR/BuiltinOps.h"
#include "llvm/ADT/ArrayRef.h"
namespace zkc::residue {
// Produce a private word-arithmetic candidate. The source stays immutable.
// Successful conversion is not correspondence, input admission or permission
// to execute; those consumers independently read the actual candidate.
mlir::OwningOpRef<mlir::ModuleOp> lowerArithmetic(mlir::ModuleOp source);
/// Propose a static pointwise tile using upstream Linalg vectorization and
/// One-Shot Bufferization. Inputs are immutable row tiles or scalar broadcasts.
/// The source has residue inputs and one residue output. This producer supplies
/// no alias, lifetime, publication or executable-kernel authority;
/// independently read the resulting private candidate before target selection
/// consumes it.
mlir::OwningOpRef<mlir::ModuleOp> proposeTile(mlir::ModuleOp source,
                                              llvm::ArrayRef<bool> rowwise,
                                              unsigned lanes);
} // namespace zkc::residue
#endif
