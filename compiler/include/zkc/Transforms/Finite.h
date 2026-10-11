#ifndef ZKC_TRANSFORMS_FINITE_H
#define ZKC_TRANSFORMS_FINITE_H
#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinOps.h"
#include "llvm/ADT/STLFunctionalExtras.h"
namespace zkc::finite {
using HelperReader =
    llvm::function_ref<mlir::FailureOr<llvm::SmallVector<mlir::Value>>(
        mlir::Operation *, mlir::ValueRange, mlir::Operation *&)>;
mlir::FailureOr<llvm::SmallVector<mlir::Value>>
realizeExpression(mlir::Operation *, mlir::ValueRange, mlir::OpBuilder &,
                  bool optimize = true);
mlir::FailureOr<llvm::SmallVector<mlir::Value>>
verifyExpression(mlir::Operation *, mlir::ValueRange, mlir::Operation *&,
                 HelperReader, mlir::Operation *symbolRoot = nullptr);
// Retain finite declarations until ordinary helper expansion/recognition.
mlir::LogicalResult realizeLocals(mlir::ModuleOp module, bool optimize = true);
// Reads actual candidate bodies; never invokes the realizer.
mlir::LogicalResult verifyRealizations(mlir::ModuleOp original,
                                       mlir::ModuleOp candidate);
} // namespace zkc::finite
#endif
