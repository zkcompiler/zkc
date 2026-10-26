#ifndef ZKC_TRANSFORMS_SCOPEDPREPARATION_H
#define ZKC_TRANSFORMS_SCOPEDPREPARATION_H

#include "FiniteVerification.h"
#include "MathematicalRecipes.h"
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Transforms/MathematicalTrace.h"
#include "llvm/ADT/DenseSet.h"

namespace zkc::mathematical {
class NumericalSelection;
}
namespace zkc::protocol {
// Finite preparation preserves ordered admission and callback effects. An
// optional mathematical proposal is compared against actual source callbacks;
// optional capacity may discard it and retry independently checked ordered
// execution. The physical transaction retains the actual prepared candidate.
// The selected recipe inventory is borrowed for the entire attempt and every
// nested callback. Independent checking does not consult this producer choice.
// Shared matching/checking work is never replenished on retry. fixedBindings
// borrows original binding declarations fixed by validated physical requests.
// With a selection context, emit one attempt and report its checking outcome;
// the enclosing physical transaction owns retry and discard accounting.
mlir::OwningOpRef<mlir::ModuleOp> prepareScopedFinite(
    mlir::ModuleOp, mathematical::RealizationWork &, uint64_t &copy,
    uint64_t &siteBytes, std::optional<CapacityCause> &capacity,
    MathematicalSelectionPolicy policy = {},
    const llvm::DenseSet<mlir::Operation *> *fixedBindings = nullptr,
    mathematical::NumericalSelection *selection = nullptr,
    mathematical::VerificationDecision *outcome = nullptr,
    const mathematical::MathematicalRecipes &recipes =
        mathematical::mathematicalRecipes(),
    mathematical::RealizationTrace *trace = nullptr);
} // namespace zkc::protocol
#endif
