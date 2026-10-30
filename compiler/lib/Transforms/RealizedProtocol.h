#ifndef ZKC_TRANSFORMS_REALIZED_PROTOCOL_H
#define ZKC_TRANSFORMS_REALIZED_PROTOCOL_H

#include "PreparedProtocol.h"
#include "zkc/Transforms/OracleSelection.h"
#include "llvm/Support/Error.h"
#include <string>

namespace zkc::mathematical {
// Private ownership of an actual-body-checked realization edge. Construction
// consumes the prepared owner; no mutable operation or untrusted record can
// become a checked edge. All modules borrow the caller's MLIR context.
//
// This is native structural correspondence, not a semantic simulation or
// authority to publish logical claims. Logical clauses and selections stay on
// the original, never on the candidate's changed signature. Production
// consumers retain this edge through execution and must interpret it before
// publishing logical claims.
class RealizedProtocol {
  PreparedProtocol prepared;
  mlir::OwningOpRef<mlir::ModuleOp> candidate;
  std::string record;
  RealizedProtocol(PreparedProtocol prepared,
                   mlir::OwningOpRef<mlir::ModuleOp> candidate,
                   std::string record)
      : prepared(std::move(prepared)), candidate(std::move(candidate)),
        record(std::move(record)) {}

public:
  static llvm::Expected<RealizedProtocol>
  realize(PreparedProtocol prepared,
          const protocol::OracleRealizationPolicy &policy = {});
  // Independent clones cannot mutate the owned checked edge. A moved-from
  // owner has no snapshots. The record view borrows this owner's lifetime.
  mlir::OwningOpRef<mlir::ModuleOp> originalSnapshot() const;
  mlir::OwningOpRef<mlir::ModuleOp> candidateSnapshot() const;
  llvm::StringRef realizationRecord() const { return record; }
  // Project an independent copy of the checked native side. Retain the edge
  // for the entire compilation; projection alone grants no logical claim.
  mlir::OwningOpRef<mlir::ModuleOp> project(bool simplify) const;
};
} // namespace zkc::mathematical

#endif
