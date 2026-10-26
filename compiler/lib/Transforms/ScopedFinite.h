#ifndef ZKC_TRANSFORMS_SCOPEDFINITE_H
#define ZKC_TRANSFORMS_SCOPEDFINITE_H

#include "MathematicalRecipes.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Transforms/Finite.h"
#include "llvm/ADT/DenseSet.h"

namespace zkc::protocol {
struct SourceExecutionClosure;
}
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
        mlir::func::FuncOp, mlir::ValueRange, llvm::StringRef,
        mlir::Operation *&)>;

// Required construction accounts shared with callback substitution. Debits
// bound each generated instruction and its CFG plumbing before allocation.
struct ScopedEmissionBudget {
  uint64_t &work;
  uint64_t &siteBytes;
  std::optional<CapacityCause> &capacity;
};

// Producer-only traversal at the caller's current scoped insertion point.
// Callback substitution uses the same builder and borrowed runtime scope.
// The caller must discard failed construction and independently check the
// actual complete candidate before publication.
mlir::FailureOr<llvm::SmallVector<mlir::Value>> realizeScopedExpression(
    mlir::Operation *source, mlir::ValueRange inputs, mlir::OpBuilder &builder,
    exec::ScopedExecutionBuilder &control, ScopedCallbackEmitter callback,
    mathematical::RealizationWork &work,
    MathematicalSelectionPolicy policy = {},
    mathematical::RealizationTrace *trace = nullptr,
    llvm::StringRef occurrence = {}, ScopedEmissionBudget *budget = nullptr,
    const protocol::SourceExecutionClosure *sourceClosure = nullptr,
    const llvm::DenseSet<mlir::Operation *> *fixedBindings = nullptr,
    const mathematical::MathematicalRecipes &recipes =
        mathematical::mathematicalRecipes());
} // namespace zkc::finite

#endif
