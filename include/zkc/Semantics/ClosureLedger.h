//===- ClosureLedger.h - producer semantic-use accounting -------*- C++ -*-===//
#ifndef ZKC_SEMANTICS_CLOSURELEDGER_H
#define ZKC_SEMANTICS_CLOSURELEDGER_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallPtrSet.h"

namespace mlir {
class Operation;
}

namespace zkc::semantics {

/// Shared accounting between producer-side reduction and terminal judgments.
/// It contains no semantic matcher: each judgment still derives its own facts.
struct ClosureLedger {
  llvm::SmallPtrSet<mlir::Operation *, 32> usedMaterialBindings;
  llvm::DenseMap<mlir::Operation *, mlir::Operation *> reductionCheckOwners;
};

} // namespace zkc::semantics

#endif // ZKC_SEMANTICS_CLOSURELEDGER_H
