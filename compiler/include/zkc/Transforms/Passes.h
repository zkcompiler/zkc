#ifndef ZKC_TRANSFORMS_PASSES_H
#define ZKC_TRANSFORMS_PASSES_H

#include "mlir/Pass/Pass.h"
#include "zkc/Contracts/Binding.h"
#include "llvm/ADT/StringRef.h"
#include <memory>

namespace mlir {
class ModuleOp;
}
namespace zkc {
struct LinearContractionStats;
namespace protocol {
/// Validate and expand whole-protocol mathematics, with optional folding.
std::unique_ptr<mlir::Pass> createPrepareProtocolPass(bool simplify = true);
/// Project the protocol profile into participant programs, retaining
/// mathematics.
std::unique_ptr<mlir::Pass> createProjectProtocolPass(bool simplify = true);
/// Lower participant mathematics to execution recipes in the exec profile.
std::unique_ptr<mlir::Pass> createLowerMathPass();
/// Distribute prefix fixing through shared sums/products and MLE leaves.
std::unique_ptr<mlir::Pass> createFixPolynomialFactorsPass();
/// Eliminate formal polynomial SSA while retaining concrete participant types.
std::unique_ptr<mlir::Pass> createEliminatePolynomialsPass();
/// Simplify total expressions in the participant profile, preserving actions.
std::unique_ptr<mlir::Pass> createSimplifyParticipantPass();
std::unique_ptr<mlir::Pass> createExpandAlgorithmsPass();
/// Select representations and kernels, converting exec to physical.
/// Selections have already been checked against the caller's retained source.
std::unique_ptr<mlir::Pass> createSelectPhysicalPass(
    protocol::Assignments selections = {}, bool linearContractions = false,
    bool releaseStorage = false, LinearContractionStats *statistics = nullptr);
} // namespace protocol
namespace relation {
/// Remove only exact duplicate normalized rows; preserve witness/public layout
/// and relation families.
std::unique_ptr<mlir::Pass> createDeduplicateRelationsPass();
} // namespace relation
} // namespace zkc
#endif
