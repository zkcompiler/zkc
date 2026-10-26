#ifndef ZKC_TRANSFORMS_SCOPEDFINITE_H
#define ZKC_TRANSFORMS_SCOPEDFINITE_H

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Transforms/Finite.h"

namespace zkc::finite {
// A reached callback can stop without producing its result. This is separate
// from construction failure and from a successful callback with no outputs.
struct ScopedCallbackResult {
  llvm::SmallVector<mlir::Value> values;
  bool stopped = false;
};
using ScopedCallbackEmitter =
    llvm::function_ref<mlir::FailureOr<ScopedCallbackResult>(
        mlir::func::FuncOp, mlir::ValueRange, llvm::StringRef,
        exec::ScopedExecutionBuilder &)>;
using ScopedCallbackReader =
    llvm::function_ref<mlir::FailureOr<ScopedCallbackResult>(
        mlir::func::FuncOp, mlir::ValueRange, mlir::Operation *&)>;

// Producer-only traversal at the caller's current scoped insertion point.
// Callback substitution uses the same builder and borrowed runtime scope.
// The caller must discard failed construction and independently check the
// actual complete candidate before publication.
mlir::FailureOr<llvm::SmallVector<mlir::Value>> realizeScopedExpression(
    mlir::Operation *source, mlir::ValueRange inputs, mlir::OpBuilder &builder,
    exec::ScopedExecutionBuilder &control, ScopedCallbackEmitter callback,
    mathematical::RealizationWork &work,
    MathematicalSelectionPolicy policy = {},
    mathematical::RealizationTrace *trace = nullptr);
} // namespace zkc::finite

#endif
