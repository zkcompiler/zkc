#ifndef ZKC_TRANSFORMS_HELPERNORMALIZATION_H
#define ZKC_TRANSFORMS_HELPERNORMALIZATION_H

#include "zkc/Dialect/Operations.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include <cstddef>
#include <memory>

namespace zkc::mathematical {
// Independent, read-only substitution and polynomial-meaning comparison.
// Keep one instance for a complete verification: calls, dead formation,
// polynomial laws and all result coordinates share its work budget and memo.
// The source root is an admitted, immutable protocol unit. Candidate bodies
// are normalization proposals with the same positional interface and symbol
// context; this internal API is not an alternative to module admission.
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
// cannot generate a body, and an unchecked body is never exposed.
class CheckedHelperNormalizations {
  mlir::Operation *root;
  HelperNormalizationChecker checker;
  mlir::SymbolTableCollection symbols;
  unsigned operations = 100000;
  uint64_t indices = 1000000, polynomial = 100000, work = 1000000;
  unsigned snapshotOperations = 100000;
  uint64_t snapshotIndices = 1000000;
  llvm::DenseMap<mlir::Operation *, mlir::OwningOpRef<mlir::func::FuncOp>>
      bodies;
  llvm::DenseMap<mlir::Operation *, mlir::OwningOpRef<mlir::func::FuncOp>>
      realizations;
  llvm::DenseSet<mlir::Operation *> visited;

public:
  explicit CheckedHelperNormalizations(mlir::Operation *sourceRoot);
  mlir::LogicalResult prepare(mlir::Operation *source);
  mlir::LogicalResult prepareRealization(mlir::func::FuncOp helper);
  mlir::func::FuncOp lookup(mlir::Operation *helper,
                            bool realization = false) const;
};
} // namespace zkc::mathematical
#endif
