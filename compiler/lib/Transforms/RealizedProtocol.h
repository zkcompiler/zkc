#ifndef ZKC_TRANSFORMS_REALIZED_PROTOCOL_H
#define ZKC_TRANSFORMS_REALIZED_PROTOCOL_H

#include "OracleRealizationFacts.h"
#include "PreparedProtocol.h"
#include "zkc/Transforms/OracleSelection.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"
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
  protocol::OracleRealizationFacts facts;
  llvm::json::Value recordData, selectionData;
  std::string record, selection;
  protocol::OracleRealizationPolicy requestedPolicy;
  RealizedProtocol(PreparedProtocol prepared,
                   mlir::OwningOpRef<mlir::ModuleOp> candidate,
                   protocol::OracleRealizationFacts facts,
                   llvm::json::Value recordData,
                   llvm::json::Value selectionData, std::string record,
                   std::string selection,
                   protocol::OracleRealizationPolicy requestedPolicy)
      : prepared(std::move(prepared)), candidate(std::move(candidate)),
        facts(std::move(facts)), recordData(std::move(recordData)),
        selectionData(std::move(selectionData)), record(std::move(record)),
        selection(std::move(selection)),
        requestedPolicy(std::move(requestedPolicy)) {}

public:
  struct ObservationSnapshot {
    mlir::OwningOpRef<mlir::ModuleOp> module;
    llvm::SmallVector<mlir::Operation *> dataExchanges;
  };
  static llvm::Expected<RealizedProtocol>
  realize(PreparedProtocol prepared,
          const protocol::OracleRealizationPolicy &policy = {});
  // Independent clones cannot mutate the owned checked edge. A moved-from
  // owner has no snapshots. The record view borrows this owner's lifetime.
  mlir::OwningOpRef<mlir::ModuleOp> preparedSnapshot() const;
  mlir::OwningOpRef<mlir::ModuleOp> authoredSnapshot() const;
  MathematicalSelectionPolicy mathematicalPolicy() const {
    return prepared.policy;
  }
  mlir::OwningOpRef<mlir::ModuleOp> candidateSnapshot() const;
  // An independent clone with exact generated opening-request associations
  // from this checked edge. This grants no new public-coin premise by itself.
  // The observation consumer must recompute after any snapshot mutation.
  llvm::Expected<ObservationSnapshot> observationSnapshot() const;
  llvm::StringRef realizationRecord() const { return record; }
  // Boundary data is exposed only to compose external publications.
  const llvm::json::Value &realizationData() const { return recordData; }
  const llvm::json::Value &normalizedSelectionData() const {
    return selectionData;
  }
  llvm::ArrayRef<protocol::OracleEntryFacts> realizationFacts() const {
    return facts.entries;
  }
  // Canonical exact inventory of actual prepared roots, with the requested
  // query order and authentication. The view borrows this owner's lifetime.
  llvm::StringRef normalizedSelection() const { return selection; }
  const protocol::OracleRealizationPolicy &oraclePolicy() const {
    return requestedPolicy;
  }
  // Project an independent copy of the checked native side. Retain the edge
  // for the entire compilation; projection alone grants no logical claim.
  mlir::OwningOpRef<mlir::ModuleOp> project(bool simplify) const;
};
} // namespace zkc::mathematical

#endif
