#ifndef ZKC_PROTOCOL_BINDING_PHYSICAL_H
#define ZKC_PROTOCOL_BINDING_PHYSICAL_H
#include "mlir/IR/BuiltinOps.h"
namespace zkc {
struct LinearContractionStats;
}
namespace zkc::protocol {
// Called after lowerPhysical admits a logical module with explicit bindings.
mlir::LogicalResult lowerBoundPhysical(
    mlir::ModuleOp,
    llvm::ArrayRef<std::pair<std::string, std::string>> selections,
    bool linearContractions, LinearContractionStats *stats);
} // namespace zkc::protocol
#endif
