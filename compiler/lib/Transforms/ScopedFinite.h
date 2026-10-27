#ifndef ZKC_TRANSFORMS_SCOPEDFINITE_H
#define ZKC_TRANSFORMS_SCOPEDFINITE_H

#include "MathematicalRecipes.h"
#include "ScopedCallback.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Transforms/Finite.h"
#include "llvm/ADT/DenseSet.h"

namespace zkc::protocol {
struct SourceExecutionClosure;
}
namespace zkc::finite {
// Required construction accounts shared with callback substitution. Debits
// bound each generated instruction and its CFG plumbing before allocation.
struct ScopedEmissionBudget {
  uint64_t &work;
  uint64_t &siteBytes;
  std::optional<CapacityCause> &capacity;
};

// Scalar/nested total recipes consume an immutable normalized callback. The
// producer supplies its original symbol root separately; detached scratch
// bodies must never resolve helpers through the destination execution owner.
using TotalRecipeEmitter =
    llvm::function_ref<mlir::FailureOr<llvm::SmallVector<mlir::Value>>(
        mlir::Operation *, mlir::ValueRange, exec::ScopedExecutionBuilder &)>;
struct CollectFold;
mlir::FailureOr<llvm::SmallVector<mlir::Value>> realizeScopedTotalExpression(
    mlir::Operation *source, mlir::Operation *sourceRoot,
    mlir::ValueRange inputs, mlir::OpBuilder &builder,
    exec::ScopedExecutionBuilder &control, TotalRecipeEmitter callback,
    mathematical::RealizationWork &work, MathematicalSelectionPolicy policy,
    mathematical::RealizationTrace *trace, ScopedEmissionBudget &budget,
    bool orderedRetry, const CollectFold *pair = nullptr,
    mlir::ValueRange consumerInputs = {});

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
        mathematical::mathematicalRecipes(),
    mlir::Operation *sumConsumer = nullptr, llvm::StringRef sumOccurrence = {},
    bool orderedRetry = false);
} // namespace zkc::finite

#endif
