#ifndef ZKC_PROTOCOL_BINDING_PHYSICAL_H
#define ZKC_PROTOCOL_BINDING_PHYSICAL_H
#include "mlir/IR/BuiltinOps.h"
namespace zkc {
struct LinearContractionStats;
}
namespace zkc::target {
class CheckedPhysicalPlan;
}
namespace zkc::protocol {
// Compare the actual physical candidate with the fresh checked logical input.
// Includes all local operands, selected kernels and per-use conversions.
llvm::Error verifyPhysicalMaterialization(mlir::ModuleOp before,
                                          mlir::ModuleOp after,
                                          const target::CheckedPhysicalPlan &);
// Transactional application; publish only after independent correspondence.
llvm::Error materializePhysical(mlir::ModuleOp,
                                const target::CheckedPhysicalPlan &);
// Called after lowerPhysical admits a logical module with explicit bindings.
mlir::LogicalResult lowerBoundPhysical(
    mlir::ModuleOp,
    llvm::ArrayRef<std::pair<std::string, std::string>> selections,
    bool linearContractions, LinearContractionStats *stats);
} // namespace zkc::protocol
#endif
