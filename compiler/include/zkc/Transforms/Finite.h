#ifndef ZKC_TRANSFORMS_FINITE_H
#define ZKC_TRANSFORMS_FINITE_H
#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Transforms/MathematicalSelection.h"
#include "zkc/Transforms/MathematicalTrace.h"
#include "zkc/Transforms/MathematicalWork.h"
#include "llvm/ADT/STLFunctionalExtras.h"
namespace zkc::finite {
using HelperReader =
    llvm::function_ref<mlir::FailureOr<llvm::SmallVector<mlir::Value>>(
        mlir::Operation *, mlir::ValueRange, mlir::Operation *&)>;
/// Reads candidate bindings in the cursor's nearest symbol table. symbolRoot
/// explicitly selects the immutable source helper table for detached source
/// bodies; null uses the source expression's nearest table. Admission and
/// checked publication remain the caller's responsibility.
mlir::FailureOr<llvm::SmallVector<mlir::Value>>
verifyExpression(mlir::Operation *, mlir::ValueRange, mlir::Operation *&,
                 HelperReader, mlir::Operation *symbolRoot = nullptr);
} // namespace zkc::finite
#endif
