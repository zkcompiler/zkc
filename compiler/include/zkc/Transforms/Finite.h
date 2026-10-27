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
/// Realize an admitted total computation after preparation assigns its unique
/// nonempty occurrence site. Refuses a missing site before editing the module.
/// Resolves source helpers in the expression's nearest symbol table and emits
/// bindings in the insertion point's nearest single-region, single-block symbol
/// table. Local control may be emitted transiently inside a conversion
/// func.func; the caller must convert it to Local and verify before
/// publication. Mutates the caller's private candidate; a failed caller must
/// discard it. Pass shared work for a containing stage; null starts a
/// standalone scope.
mlir::FailureOr<llvm::SmallVector<mlir::Value>>
realizeExpression(mlir::Operation *, mlir::ValueRange, mlir::OpBuilder &,
                  MathematicalSelectionPolicy policy = {},
                  mathematical::RealizationWork *work = nullptr,
                  mathematical::RealizationTrace *trace = nullptr,
                  bool orderedRetry = false);
/// Reads candidate bindings in the cursor's nearest symbol table. symbolRoot
/// explicitly selects the immutable source helper table for detached source
/// bodies; null uses the source expression's nearest table. Admission and
/// checked publication remain the caller's responsibility.
mlir::FailureOr<llvm::SmallVector<mlir::Value>>
verifyExpression(mlir::Operation *, mlir::ValueRange, mlir::Operation *&,
                 HelperReader, mlir::Operation *symbolRoot = nullptr);
} // namespace zkc::finite
#endif
