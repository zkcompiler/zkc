#ifndef ZKC_TARGET_SOURCE_H
#define ZKC_TARGET_SOURCE_H
#include "zkc/Dialect/IR.h"
#include "zkc/Target/Json.h"
namespace zkc {
class SourceLibraryInterface;
/// Decode the program's logical context and resolve its installed library.
/// The interface borrows the MLIR context, independently of a target wire
/// format.
llvm::Expected<const SourceLibraryInterface *>
resolveProgramLibrary(mlir::Operation *program);
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>>
importSource(const llvm::json::Value &request, mlir::MLIRContext &context);
llvm::Expected<llvm::json::Value> exportPlan(mlir::ModuleOp module);
/// Lower finite source-library programs. Other top-level operations are
/// refused.
mlir::LogicalResult lowerToPlan(mlir::ModuleOp module);
} // namespace zkc
#endif
