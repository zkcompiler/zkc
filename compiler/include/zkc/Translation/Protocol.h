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
/// context from that registry, then context.loadAllAvailableDialects().
/// Locations are diagnostic metadata, never evidence of source correspondence.
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
/// Reconstruct and admit the complete root, including generated relations.
/// This is checked export; local operation invariants alone are insufficient.
llvm::Expected<source::Content> exportSource(mlir::Operation *);
llvm::Expected<llvm::json::Value> exportModule(mlir::Operation *);
} // namespace zkc::protocol
#endif
