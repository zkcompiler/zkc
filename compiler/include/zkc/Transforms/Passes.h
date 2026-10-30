#ifndef ZKC_TRANSFORMS_PASSES_H
#define ZKC_TRANSFORMS_PASSES_H

#include "mlir/Pass/Pass.h"
#include "zkc/Contracts/Binding.h"
#include "zkc/Target/Selection.h"
#include "zkc/Transforms/MathematicalSelection.h"
#include "llvm/ADT/StringRef.h"
#include <memory>

namespace mlir {
class ModuleOp;
}
namespace zkc {
/// Read-only complete stage admission at the owning module scope. Run before
/// generic rewrites and after transformations before publishing a candidate.
std::unique_ptr<mlir::Pass> createAdmitStagePass();
namespace mathematical {
struct RealizationTrace;
}
struct LinearContractionStats;
namespace protocol {
/// Trace/statistics observers passed to these factories are borrowed for
/// synchronous invocation. A caller that schedules concurrent copies must use
/// separate observers; they are not pass-managed analyses.
/// Admit source mathematics, realize polynomial recipes, expand protocol
/// applications and prepare participant mathematics, with optional folding.
/// Retain scoped definitions and finite requests for executable selection.
std::unique_ptr<mlir::Pass>
createPrepareProtocolPass(bool simplify = true,
                          MathematicalSelectionPolicy policy = {},
                          mathematical::RealizationTrace *trace = nullptr);
/// Project the protocol profile into participant programs, retaining
/// mathematics.
std::unique_ptr<mlir::Pass>
createProjectProtocolPass(bool simplify = true,
                          MathematicalSelectionPolicy policy = {});
/// Form demanded participant mathematics as closed computation units in Exec.
std::unique_ptr<mlir::Pass>
createLowerMathPass(MathematicalSelectionPolicy policy = {},
                    mathematical::RealizationTrace *trace = nullptr);
/// Distribute prefix fixing through shared sums/products and MLE leaves.
std::unique_ptr<mlir::Pass> createFixPolynomialFactorsPass();
/// Eliminate formal polynomial SSA while retaining concrete participant types.
std::unique_ptr<mlir::Pass> createEliminatePolynomialsPass();
/// Simplify total expressions in the participant profile, preserving actions.
std::unique_ptr<mlir::Pass> createSimplifyParticipantPass();
/// Select representations and kernels, converting exec to physical.
/// Selections have already been checked against the caller's retained source.
std::unique_ptr<mlir::Pass> createSelectPhysicalPass(
    protocol::Assignments selections = {}, bool linearContractions = false,
    bool releaseStorage = false, LinearContractionStats *statistics = nullptr,
    llvm::ArrayRef<target::FunctionPortSelection> functionPorts = {},
    MathematicalSelectionPolicy numericalPolicy = {},
    const target::CpuTarget &cpuTarget = {});
} // namespace protocol
namespace computation {
/// Realize logical numerical units into scoped Func/CF execution before
/// physical planning. This is a separate independently checked Exec edge.
std::unique_ptr<mlir::Pass>
createRealizeComputationsPass(MathematicalSelectionPolicy policy = {},
                              mathematical::RealizationTrace *trace = nullptr);
} // namespace computation
namespace relation {
/// Remove only exact duplicate normalized rows; preserve witness/public layout
/// and relation families.
std::unique_ptr<mlir::Pass> createDeduplicateRelationsPass();
} // namespace relation
} // namespace zkc
#endif
