#ifndef ZKC_PROTOCOL_BINDING_PHYSICAL_H
#define ZKC_PROTOCOL_BINDING_PHYSICAL_H
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Target/Selection.h"
#include "zkc/Transforms/MathematicalSelection.h"
namespace zkc {
struct LinearContractionStats;
}
namespace zkc::target {
class CheckedPhysicalPlan;
}
namespace zkc::protocol {
// Freshness-check the original input, then compare actual physical output with
// the checked plan's selected executable subject. Numerical correspondence from
// original numerical source to that privately retained subject was
// independently established by validation. Includes participant/source
// preservation, all local operands, selected implementations and per-use
// conversions.
llvm::Error verifyPhysicalMaterialization(mlir::ModuleOp before,
                                          mlir::ModuleOp after,
                                          const target::CheckedPhysicalPlan &);
// Transactional application; publish only after independent correspondence.
llvm::Error materializePhysical(mlir::ModuleOp,
                                const target::CheckedPhysicalPlan &);
// Called after lowerPhysical admits the original logical module. Kernel
// realization remains private plan state until checked physical publication.
mlir::LogicalResult lowerBoundPhysical(
    mlir::ModuleOp,
    llvm::ArrayRef<std::pair<std::string, std::string>> selections,
    bool linearContractions, LinearContractionStats *stats,
    bool releaseStorage = false,
    llvm::ArrayRef<target::FunctionPortSelection> functionPorts = {},
    MathematicalSelectionPolicy numericalPolicy = {},
    const target::CpuTarget &cpuTarget = {});
} // namespace zkc::protocol
#endif
