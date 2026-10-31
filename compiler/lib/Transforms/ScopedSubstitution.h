#ifndef ZKC_TRANSFORMS_SCOPEDSUBSTITUTION_H
#define ZKC_TRANSFORMS_SCOPEDSUBSTITUTION_H

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Analysis/ComputationWork.h"
#include "llvm/ADT/DenseMap.h"

namespace zkc::mathematical {
class NumericalSelection;
// Producer-only substitution into a private, admitted source. The selected
// scoped bodies already carry their concrete occurrence sites. Their root
// returns borrow the caller's scope and introduce no completion charge.
// The independent numerical reader checks the final candidate against the
// original mathematical requests; this map is never evidence for that reader.
// Full-input admission inspection spends cumulative numerical context checking.
// Actual declaration clones and logical scoped expansion spend construction.
// Inspection exhaustion is required, including in speculative construction.
mlir::OwningOpRef<mlir::ModuleOp> substituteScopedComputations(
    mlir::ModuleOp source,
    const llvm::DenseMap<mlir::Operation *, mlir::func::FuncOp> &replacements,
    NumericalSelection &selection,
    std::optional<CapacityCause> *capacity = nullptr);
} // namespace zkc::mathematical
#endif
