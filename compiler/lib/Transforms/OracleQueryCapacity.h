#ifndef ZKC_TRANSFORMS_ORACLEQUERYCAPACITY_H
#define ZKC_TRANSFORMS_ORACLEQUERYCAPACITY_H
#include "mlir/IR/BuiltinOps.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Support/Error.h"
#include <cstdint>
namespace zkc::protocol {
struct OracleQuerySize {
  uint64_t leaves = 0;
  uint64_t nodes = 0;
  bool operator==(const OracleQuerySize &other) const {
    return leaves == other.leaves && nodes == other.nodes;
  }
};
struct OracleQueryCapacity {
  // Borrowed operations in the immutable prepared entry. Absent unreachable
  // occurrences have bound zero. Counts include duplicate and unused queries.
  llvm::DenseMap<mlir::Operation *, OracleQuerySize> constructors;
  llvm::DenseMap<mlir::Operation *, OracleQuerySize> queries;
};
// Read source structure, never positions, answers, data or validity predicates.
// Bounds range over every possible admitted repeat count. A known uniform
// count tightens the maximum; role-dependent values and carried initializers
// do not. Joins retain loop backedges and sequence selections. Overflow or
// exhausted analysis work refuses the
// compilation; it does not add a source premise or a logical execution stop.
// This analysis does not authorize replacing an actual reference by an origin.
llvm::Expected<OracleQueryCapacity>
analyzeOracleQueryCapacity(mlir::ModuleOp prepared, llvm::StringRef entry,
                           uint64_t work = 1000000);
} // namespace zkc::protocol
#endif
