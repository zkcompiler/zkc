#ifndef ZKC_TRANSFORMS_STRUCTUREDCOMPUTATION_H
#define ZKC_TRANSFORMS_STRUCTUREDCOMPUTATION_H

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"
#include "llvm/ADT/ArrayRef.h"

namespace zkc::mathematical {
/// A rank-one map, optionally followed by an exact field sum. Tensor arguments
/// are immutable values with equal lengths; scalar arguments are broadcasts.
/// The execution boundary must check every length before invoking this profile.
/// The mathematical interpretation includes empty tensors and an empty sum of
/// zero. Runtime allocation and resource refusal are separate contracts.
enum class StructuredResult { Map, Sum };

/// Construct a private Func/Tensor/Linalg candidate from a closed scalar field
/// formula. Each input slot is retained even if unused. This producer is not
/// evidence that the candidate realizes that formula.
mlir::OwningOpRef<mlir::ModuleOp>
proposeStructuredComputation(mlir::Block &formula, llvm::ArrayRef<bool> rowwise,
                             StructuredResult result);

/// Apply upstream CSE/DCE to the scalar region. A candidate must be read again
/// afterwards, and after any subsequent mutation. No persisted approval bit.
mlir::LogicalResult optimizeStructuredComputation(mlir::ModuleOp candidate);

/// Independently read the actual candidate's complete schema, tensor axes,
/// iteration kind, seed, ports, scalar expression and returned value. Compare
/// scalar DAGs by ordered labelled bisimulation, allowing sharing/dead-code
/// changes but no unsupported algebraic identities. Never calls the producer.
mlir::LogicalResult verifyStructuredComputation(mlir::Block &formula,
                                                llvm::ArrayRef<bool> rowwise,
                                                StructuredResult result,
                                                mlir::ModuleOp candidate);

/// Consume the actual admitted Linalg body as a closed scalar function for the
/// current typed native map/reduction handlers. Rechecks source correspondence
/// before extracting the candidate; does not regenerate the original formula.
mlir::OwningOpRef<mlir::func::FuncOp>
consumeStructuredComputation(mlir::Block &formula, llvm::ArrayRef<bool> rowwise,
                             StructuredResult result, mlir::ModuleOp candidate);
} // namespace zkc::mathematical
#endif
