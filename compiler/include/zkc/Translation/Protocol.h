#ifndef ZKC_TRANSLATION_PROTOCOL_H
#define ZKC_TRANSLATION_PROTOCOL_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Source/Model.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/Support/JSON.h"
#include <string>
#include <vector>

namespace zkc::protocol {
/// Import requires loaded dialects: registerDialects(registry), construct the
/// context from that registry, then context.loadAllAvailableDialects(). A
/// missing built-in dialect returns DialectRegistrationError
/// (Dialect/Registry.h), an invocation precondition failure; import never loads
/// dialects. Locations are diagnostic metadata, never evidence of source
/// correspondence.
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>> importModule(
    const source::Content &, mlir::MLIRContext &,
    llvm::function_ref<mlir::Location(const source::Node &)> locations = {},
    const source::Node **failureLocation = nullptr);
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>> importModule(
    const source::Module &, mlir::MLIRContext &,
    llvm::function_ref<mlir::Location(const source::Node &)> locations = {},
    const source::Node **failureLocation = nullptr);
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>> importModule(
    const source::Participants &, mlir::MLIRContext &,
    llvm::function_ref<mlir::Location(const source::Node &)> locations = {},
    const source::Node **failureLocation = nullptr);
/// Decode actual native program bytes and independently compare their
/// executable view to physical SSA, including local bodies, bindings, services
/// and entries. Allows SSA renaming. Locations, projection/relation
/// declarations, implicit immutable capture forwarding and argument display
/// names are not serialized.
llvm::Error verifyProgramArtifact(mlir::Operation *subject,
                                  llvm::StringRef bytes);
/// Reconstruct and admit the complete root, including generated relations.
/// This is checked export; local operation invariants alone are insufficient.
llvm::Expected<source::Content> exportSource(mlir::Operation *);
llvm::Expected<llvm::json::Value> exportModule(mlir::Operation *);
} // namespace zkc::protocol
#endif
