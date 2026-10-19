#ifndef ZKC_ANALYSIS_TOTALCLOSURE_H
#define ZKC_ANALYSIS_TOTALCLOSURE_H
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/SymbolTable.h"
#include "llvm/ADT/BitVector.h"
#include <cstdint>
#include <memory>
#include <set>
#include <vector>

namespace zkc::mathematical {
// Formal-position dependencies include unused intermediate computations. A
// Protocol consumer interprets them as role availability; a numerical owner
// uses the same closed mathematics without introducing roles.
struct TotalSummary {
  llvm::SmallVector<llvm::BitVector> results;
  std::set<std::vector<unsigned>> requirements;
  unsigned expandedOperations = 0;
  unsigned depth = 1;
  uint64_t replayIndices = 0;
  bool observesPolynomial = false;
};
// Bounded, read-only analysis of one stable symbol table. The optional public
// entry is explicit; every other mathematical function must be private. The
// containing dialect owns its declaration vocabulary and entry count.
// Destroy this analysis before changing any inspected body or symbol table.
// A failed query invalidates the analysis; subsequent queries also fail.
class TotalClosure {
  struct Impl;
  std::unique_ptr<Impl> impl;

public:
  TotalClosure(mlir::Operation *owner, mlir::SymbolTableCollection &symbols,
               mlir::func::FuncOp entry = {});
  ~TotalClosure();
  // Check the semantic closure of all retained helpers/domains, including
  // unused ones. As in an enclosing MLIR verifier, local operation/type
  // invariants and SSA/symbol-table formation must already hold. This is not a
  // raw IR parser. Unknown bounds for formal polynomial inputs remain caller
  // obligations; admission alone does not discharge those observations.
  mlir::LogicalResult verify();
  // Query under the owner's already checked domain/SSA closure. One shared
  // budget covers all queries; returned summaries live with this analysis.
  mlir::LogicalResult get(mlir::func::FuncOp function,
                          const TotalSummary *&result);
  mlir::LogicalResult get(mlir::func::CallOp call, const TotalSummary *&result);
};
mlir::LogicalResult verifyTotalClosure(mlir::Operation *owner,
                                       mlir::func::FuncOp entry = {});
} // namespace zkc::mathematical
#endif
