#ifndef ZKC_TRANSLATION_TABLE_H
#define ZKC_TRANSLATION_TABLE_H
#include "zkc/Dialect/IR.h"
#include "zkc/Support/Json.h"
namespace zkc {
class SourceLibraryInterface;
/// Decode the program's logical context and resolve its installed library.
/// The interface borrows the MLIR context, independently of a target wire
/// format.
llvm::Expected<const SourceLibraryInterface *>
resolveProgramLibrary(mlir::Operation *program);
/// Load the registered dialects and source library models before import.
/// For the built-in table model, use registerTableLibrary(registry) alongside
/// registerDialects(registry), then context.loadAllAvailableDialects().
/// Missing PIR registration/loading returns DialectRegistrationError
/// (Dialect/Registry.h), independently of source admission.
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>>
importSource(const llvm::json::Value &request, mlir::MLIRContext &context);
llvm::Expected<llvm::json::Value> exportPlan(mlir::ModuleOp module);
} // namespace zkc
#endif
