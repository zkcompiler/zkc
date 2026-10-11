#ifndef ZKC_TRANSFORMS_NESTED_CONTRACTIONS_H
#define ZKC_TRANSFORMS_NESTED_CONTRACTIONS_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/MathematicalSelection.h"

namespace zkc::nested {
/// Checked collection of all matrix row/column contractions. Run in the
/// structured preparation window, after transparent helper expansion and before
/// finite::realizeLocals. Owns an immutable source, candidate clone,
/// independent check and publication. Unsupported/disabled collections remain
/// unchanged. Only outer finite declarations are replaced; inner declarations
/// and the surrounding definitions survive. Publication invalidates borrowed IR
/// views. The relation preserves ordered logical admission under the installed
/// native primitive interpretation and sufficient capacity, not resource
/// identity.
/// Thread the same expansion state through this rewrite and Finish expansion;
/// it retains inner admission guard origins and cumulative naming budgets.
/// Requires a retained, unfinished state from RetainMaps on this subject,
/// including when the collection policy is disabled. Invalid lifecycle states
/// are refused without changing the module or state.
mlir::LogicalResult
rewriteFiniteCollections(mlir::ModuleOp module,
                         protocol::AlgorithmExpansionState &state,
                         MathematicalSelectionPolicy policy = {});

/// Raw pre-expansion IR entry, only for modules with no prior helper
/// expansion paths. Uses a temporary origin record for the checked rewrite.
/// Callers retaining origins through Finish must use the staged overload above.
mlir::LogicalResult
rewriteFiniteCollections(mlir::ModuleOp module,
                         MathematicalSelectionPolicy policy = {});

/// Independently reads the actual source domains, callback operands, scalar
/// laws, seeds, candidate control and unchanged context. Does not invoke the
/// optimizer's recognizers or accept a selection plan as evidence. Identity is
/// an accepted result. Both modules must retain the original helper closure.
/// This overload has no prior expansion paths; use the stateful overload after
/// RetainMaps when call sites may already encode helper expansion.
mlir::LogicalResult verifyFiniteCollections(mlir::ModuleOp source,
                                            mlir::ModuleOp candidate);
/// Also checks retained occurrence paths and budgets in staged preparation.
/// Both states must be retained and unfinished; invalid lifecycle states are
/// refused without changing either module or state.
mlir::LogicalResult verifyFiniteCollections(
    mlir::ModuleOp source, mlir::ModuleOp candidate,
    const protocol::AlgorithmExpansionState &sourceState,
    const protocol::AlgorithmExpansionState &candidateState);
} // namespace zkc::nested
#endif
