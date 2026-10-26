#ifndef ZKC_TRANSFORMS_SCOPEDPREPARATION_H
#define ZKC_TRANSFORMS_SCOPEDPREPARATION_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Transforms/MathematicalTrace.h"

namespace zkc::protocol {
// Ordered finite preparation gives every callback occurrence its own actual
// mathematical requests. It neither selects pure recipes nor drops stopped
// execution. The actual candidate is retained by the physical transaction;
// validation composes this reader with numerical correspondence.
mlir::OwningOpRef<mlir::ModuleOp>
prepareScopedFinite(mlir::ModuleOp, mathematical::RealizationWork &,
                    uint64_t &copy, uint64_t &siteBytes,
                    std::optional<CapacityCause> &capacity);
mlir::LogicalResult
verifyScopedFinitePreparation(mlir::ModuleOp source, mlir::ModuleOp candidate,
                              mathematical::RealizationWork &work);
} // namespace zkc::protocol
#endif
