#ifndef ZKC_TRANSFORMS_NESTED_CONTRACTIONS_H
#define ZKC_TRANSFORMS_NESTED_CONTRACTIONS_H

#include "mlir/IR/BuiltinOps.h"
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
mlir::LogicalResult
rewriteFiniteCollections(mlir::ModuleOp module,
                         MathematicalSelectionPolicy policy = {});

/// Independently reads the actual source domains, callback operands, scalar
/// laws, seeds, candidate control and unchanged context. Does not invoke the
/// optimizer's recognizers or accept a selection plan as evidence. Identity is
/// an accepted result. Both modules must retain the original helper closure.
mlir::LogicalResult verifyFiniteCollections(mlir::ModuleOp source,
                                            mlir::ModuleOp candidate);
} // namespace zkc::nested
#endif
