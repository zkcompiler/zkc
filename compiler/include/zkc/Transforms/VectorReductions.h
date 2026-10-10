#ifndef ZKC_TRANSFORMS_VECTORREDUCTIONS_H
#define ZKC_TRANSFORMS_VECTORREDUCTIONS_H
#include "zkc/Transforms/Algorithms.h"

namespace zkc::mathematical {
/// Explicitly selected, transactional multiply-map/native-sum fusion on the
/// retained output of RetainMaps. Preserves values and ordered shape refusals
/// under sufficient resources, including source occurrences and unused rows.
/// Does not promise equal exhaustion, arbitrary backend failures or memory use.
/// Other map/reducer shapes remain on the ordinary realization path.
mlir::LogicalResult fuseVectorReductions(mlir::ModuleOp,
                                         protocol::AlgorithmExpansionState &);
/// Reads the immutable original and actual candidate, without running the
/// producer. Checks guards, contracts, slots, sites, result substitution,
/// surrounding code, declaration inventory and full occurrence records.
mlir::LogicalResult verifyVectorReductionsPreserved(
    mlir::ModuleOp original, mlir::ModuleOp candidate,
    const protocol::AlgorithmExpansionState &originalState,
    const protocol::AlgorithmExpansionState &candidateState);
} // namespace zkc::mathematical
#endif
