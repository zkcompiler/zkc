#ifndef ZKC_TRANSFORMS_KERNEL_QUOTIENT_H
#define ZKC_TRANSFORMS_KERNEL_QUOTIENT_H

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Transforms/MathematicalWork.h"
#include "zkc/heir/Admission.h"

namespace zkc::kernel {
void registerQuotientDialects(mlir::DialectRegistry &registry);
// These readers interpret actual source/native SSA. Neither calls an importer,
// placement pass, recipe producer or transformation replay.
mlir::FailureOr<heir::ArithmeticMeaning>
readQuotientSource(mlir::func::FuncOp source, uint64_t &remaining,
                   llvm::ArrayRef<unsigned> variables = {},
                   bool *exhausted = nullptr);
mlir::FailureOr<llvm::SmallVector<mlir::Value>>
readQuotientExecution(mlir::func::FuncOp source, mlir::Operation *targetRoot,
                      llvm::StringRef rootSite, mlir::ValueRange arguments,
                      mlir::Operation *&cursor, uint64_t &remaining,
                      bool *exhausted = nullptr, uint64_t *siteBytes = nullptr);
// An empty successful result means that optional placement was unavailable.
// A failure means a malformed candidate or a correspondence mismatch, and is
// terminal. All speculative work is charged before publication.
mlir::FailureOr<mlir::OwningOpRef<mlir::ModuleOp>>
proposeQuotientExecution(mlir::func::FuncOp source,
                         mathematical::RealizationWork &work);
} // namespace zkc::kernel
#endif
