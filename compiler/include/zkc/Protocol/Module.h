#ifndef ZKC_PROTOCOL_MODULE_H
#define ZKC_PROTOCOL_MODULE_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Source/Model.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/Support/JSON.h"
#include <string>
#include <vector>

namespace zkc {
struct LinearContractionStats;
}
namespace zkc::protocol {
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
llvm::Expected<source::Content> exportSource(mlir::Operation *);
llvm::Expected<llvm::json::Value> exportModule(mlir::Operation *);
mlir::LogicalResult verifyModule(mlir::Operation *);
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>> project(mlir::ModuleOp);
mlir::LogicalResult lowerPhysical(
    mlir::ModuleOp,
    llvm::ArrayRef<std::pair<std::string, std::string>> selections = {},
    bool linearContractions = false, LinearContractionStats *stats = nullptr,
    bool releaseStorage = false);
/// Insert releases after last SSA use in admitted one-block physical locals.
mlir::LogicalResult releaseLocalStorage(mlir::ModuleOp);
} // namespace zkc::protocol
#endif
