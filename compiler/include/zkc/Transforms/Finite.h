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
/// Mutates the caller's private candidate; a failed caller must discard it.
/// Pass shared work for a containing stage; null starts a standalone scope.
mlir::FailureOr<llvm::SmallVector<mlir::Value>>
realizeExpression(mlir::Operation *, mlir::ValueRange, mlir::OpBuilder &,
                  MathematicalSelectionPolicy policy = {},
                  mathematical::RealizationWork *work = nullptr,
                  mathematical::RealizationTrace *trace = nullptr);
mlir::FailureOr<llvm::SmallVector<mlir::Value>>
verifyExpression(mlir::Operation *, mlir::ValueRange, mlir::Operation *&,
                 HelperReader, mlir::Operation *symbolRoot = nullptr);
// Retain finite declarations until ordinary helper expansion/recognition.
// Publishes only a checked candidate; all definitions share work. A null work
// argument starts a standalone scope for this invocation.
mlir::LogicalResult
realizeLocals(mlir::ModuleOp module, MathematicalSelectionPolicy policy = {},
              mathematical::RealizationWork *work = nullptr,
              mathematical::RealizationTrace *trace = nullptr);
// Reads actual candidate bodies; never invokes the realizer.
mlir::LogicalResult verifyRealizations(mlir::ModuleOp original,
                                       mlir::ModuleOp candidate);
} // namespace zkc::finite
#endif
