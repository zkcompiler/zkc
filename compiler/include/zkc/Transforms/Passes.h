#ifndef ZKC_TRANSFORMS_PASSES_H
#define ZKC_TRANSFORMS_PASSES_H

#include "mlir/Pass/Pass.h"
#include "zkc/Source/Model.h"
#include "llvm/ADT/StringRef.h"
#include <memory>

namespace mlir {
class ModuleOp;
}
namespace zkc {
/// Lower finite source-library programs; refuse other top-level operations.
mlir::LogicalResult lowerToPlan(mlir::ModuleOp module);
std::unique_ptr<mlir::Pass> createLowerPIRToPlanPass();
std::unique_ptr<mlir::Pass>
createLowerPlanToPhysicalPass(llvm::StringRef mode = "lazy");
std::unique_ptr<mlir::Pass> createSimplifyTableRegionsPass();
namespace protocol {
std::unique_ptr<mlir::Pass> createExpandAlgorithmsPass();
std::unique_ptr<mlir::Pass> createProjectParticipantsPass();
/// Selections have already been checked against the caller's retained source.
std::unique_ptr<mlir::Pass>
createPlanParticipantsPass(source::Assignments selections = {},
                           bool linearContractions = false,
                           bool releaseStorage = false);
} // namespace protocol
namespace relation {
/// Remove only exact duplicate normalized rows; preserve witness/public layout
/// and relation families.
std::unique_ptr<mlir::Pass> createDeduplicateRelationsPass();
} // namespace relation
/// Register built-in passes. Tools opt into registration; linking the library
/// does not mutate MLIR's global pass registry.
void registerCompilerPasses();
} // namespace zkc
#endif
