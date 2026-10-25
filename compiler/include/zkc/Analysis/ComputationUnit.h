#ifndef ZKC_ANALYSIS_COMPUTATION_UNIT_H
#define ZKC_ANALYSIS_COMPUTATION_UNIT_H

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"

namespace zkc::mathematical {
/// Identifies a requested profile, not evidence that the body is admitted.
bool isComputationUnit(mlir::Operation *operation);
/// Inspect the public entry without assuming nested declaration invariants.
/// A missing, ambiguous or malformed entry has no result.
mlir::func::FuncOp getComputationEntry(mlir::ModuleOp unit);
/// Full closed-computation admission after ordinary nested MLIR verification.
/// Includes unused declarations; the profile marker alone grants no authority.
mlir::LogicalResult verifyComputationUnit(mlir::ModuleOp unit);
} // namespace zkc::mathematical

#endif
