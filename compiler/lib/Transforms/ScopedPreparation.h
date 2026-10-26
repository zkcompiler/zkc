#ifndef ZKC_TRANSFORMS_SCOPEDPREPARATION_H
#define ZKC_TRANSFORMS_SCOPEDPREPARATION_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Transforms/MathematicalTrace.h"
#include "llvm/ADT/DenseSet.h"

namespace zkc::protocol {
// Finite preparation preserves ordered admission and callback effects. An
// optional mathematical proposal is compared against actual source callbacks;
// optional capacity may discard it and retry independently checked ordered
// execution. The physical transaction retains the actual prepared candidate.
// Shared matching/checking work is never replenished on retry. fixedBindings
// borrows original binding declarations fixed by validated physical requests.
mlir::OwningOpRef<mlir::ModuleOp> prepareScopedFinite(
    mlir::ModuleOp, mathematical::RealizationWork &, uint64_t &copy,
    uint64_t &siteBytes, std::optional<CapacityCause> &capacity,
    MathematicalSelectionPolicy policy = {},
    const llvm::DenseSet<mlir::Operation *> *fixedBindings = nullptr);
mlir::LogicalResult verifyScopedFinitePreparation(
    mlir::ModuleOp source, mlir::ModuleOp candidate,
    mathematical::RealizationWork &work,
    MathematicalSelectionPolicy policy = {},
    mathematical::VerificationDecision *outcome = nullptr,
    const llvm::DenseSet<mlir::Operation *> *fixedBindings = nullptr);
} // namespace zkc::protocol
#endif
