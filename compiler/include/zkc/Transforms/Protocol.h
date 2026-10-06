#ifndef ZKC_TRANSFORMS_PROTOCOL_H
#define ZKC_TRANSFORMS_PROTOCOL_H

#include "mlir/IR/BuiltinOps.h"
#include "llvm/Support/Error.h"
#include <string>
#include <utility>

namespace zkc {
struct LinearContractionStats;
}
namespace zkc::protocol {
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>> project(mlir::ModuleOp);
mlir::LogicalResult lowerPhysical(
    mlir::ModuleOp,
    llvm::ArrayRef<std::pair<std::string, std::string>> selections = {},
    bool linearContractions = false, LinearContractionStats *stats = nullptr,
    bool releaseStorage = false);
/// Check that a physical candidate only inserts admitted storage releases,
/// preserving the positions and operands of existing releases.
/// Preserves computation under sufficient capacity, not equal heap high water
/// marks or outcomes at arbitrary native resource caps.
mlir::LogicalResult verifyStoragePreserved(mlir::ModuleOp before,
                                           mlir::ModuleOp after);
/// Insert releases after last SSA use in admitted one-block physical locals.
mlir::LogicalResult releaseLocalStorage(mlir::ModuleOp);
} // namespace zkc::protocol
#endif
