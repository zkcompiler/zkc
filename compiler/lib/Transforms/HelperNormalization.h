#ifndef ZKC_TRANSFORMS_HELPERNORMALIZATION_H
#define ZKC_TRANSFORMS_HELPERNORMALIZATION_H

#include "Computation/NormalizationVerification.h"
#include "zkc/Analysis/ComputationWork.h"
#include "zkc/Dialect/Operations.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include <cstddef>
#include <memory>

namespace zkc::mathematical {
// Bounded ordinary MLIR folds; independent readers interpret original packs.
mlir::LogicalResult
foldArrayProjections(mlir::Block &, uint64_t &work,
                     OptimizationOutcome *outcome = nullptr);

// Independent, read-only substitution and polynomial-meaning comparison.
// Keep one instance for a complete verification: calls, dead formation,
// polynomial laws and all result coordinates share its work budget and memo.
// The source root is an admitted, immutable Protocol or Kernel symbol table.
// Candidate bodies are normalization proposals with the same positional
// interface and symbol context; this internal API is not an alternative to
// module admission.
class HelperNormalizationChecker {
  struct Implementation;
  std::unique_ptr<Implementation> implementation;

public:
  explicit HelperNormalizationChecker(mlir::Operation *sourceRoot,
                                      size_t work = 4000000);
  ~HelperNormalizationChecker();
  mlir::LogicalResult check(mlir::func::FuncOp source, mlir::Block &candidate);
};

// Producer-owned proposals, independently checked before becoming recipe
// inputs. This is ordinary temporary MLIR, never a second editable IR model.
// Preparation is separate from the read-only recipe verifier. Its lookup
// cannot generate a body, and an unchecked body is never exposed. Discard the
// scope if preparation fails; checked bodies are immutable while in use.
class CheckedHelperNormalizations {
  mlir::Operation *root;
  HelperNormalizationChecker checker;
  computation::NormalizationProvenanceChecker provenance;
  mlir::SymbolTableCollection symbols;
  unsigned operations = 100000, snapshotOperations = 100000;
  uint64_t snapshotIndices = 1000000;
  uint64_t indices = 1000000, polynomial = 100000, work = 1000000;
  llvm::DenseMap<mlir::Operation *, mlir::OwningOpRef<mlir::func::FuncOp>>
      bodies;
  llvm::DenseSet<mlir::Operation *> visited;
  llvm::DenseSet<mlir::Operation *> polynomialGenerated;

public:
  explicit CheckedHelperNormalizations(mlir::Operation *sourceRoot);
  mlir::LogicalResult prepare(mlir::Operation *source);
  // Exact, bounded snapshots for a retained normalized Kernel closure. This
  // reader performs exact substitution only; it never folds, eliminates
  // polynomials or proposes optimizations.
  // Failure refuses an unsupported structural closure or exhausted bound.
  mlir::LogicalResult readback(uint64_t *remaining = nullptr);
  mlir::func::FuncOp lookup(mlir::Operation *helper) const;
  bool isPolynomialGenerated(mlir::Operation *operation) const {
    return polynomialGenerated.contains(operation);
  }
};
} // namespace zkc::mathematical
#endif
