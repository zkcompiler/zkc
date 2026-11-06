#ifndef ZKC_ANALYSIS_FINITECLOSURE_H
#define ZKC_ANALYSIS_FINITECLOSURE_H

#include "mlir/IR/OwningOpRef.h"
#include "mlir/IR/SymbolTable.h"
#include "zkc/Analysis/Finite.h"

namespace zkc::finite {
// Structural classes of closed executable definitions in an immutable
// analysis. Class references live only in the analysis's expression terms.
class ClosureClasses {
public:
  mlir::LogicalResult resolveEdges(mlir::Operation *op,
                                   mlir::NamedAttrList &attributes,
                                   mlir::SymbolTableCollection &symbols,
                                   llvm::function_ref<bool(uint64_t)> charge);

private:
  struct Representative {
    mlir::OwningOpRef<mlir::Operation *> definition;
    uint64_t size;
    unsigned id;
  };
  llvm::DenseMap<mlir::Operation *, unsigned> known;
  llvm::DenseSet<mlir::Operation *> active;
  llvm::DenseMap<size_t, llvm::SmallVector<Representative, 1>> classes;
  unsigned next = 0;

  mlir::FailureOr<unsigned> classify(mlir::Operation *definition,
                                     mlir::SymbolTableCollection &symbols,
                                     llvm::function_ref<bool(uint64_t)> charge);
};
} // namespace zkc::finite
#endif
