//===- ProtocolFacts.h - judgment-free protocol body facts -----*- C++ -*-===//
#ifndef ZKC_SEMANTICS_PROTOCOLFACTS_H
#define ZKC_SEMANTICS_PROTOCOLFACTS_H

#include "zkc/Dialect/Pir/PirOps.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringMap.h"

#include <utility>

namespace zkc::semantics {

/// A non-owning, judgment-free index of one protocol body at one IR epoch.
///
/// Facts preserve malformed collisions instead of choosing a winner.  A
/// consumer that needs uniqueness must establish that judgment itself.  The
/// index deliberately does not assign canonical event numbers; identity and
/// endpoint consumers use encoding::canonicalIndex for that distinct order.
class ProtocolFacts {
public:
  using Occurrences =
      llvm::DenseMap<int64_t, llvm::SmallVector<mlir::Operation *, 1>>;
  using Roles = llvm::StringMap<Occurrences>;
  using Memberships = llvm::StringMap<Roles>;

  static ProtocolFacts compute(mlir::Block &body);

  llvm::ArrayRef<pir::ReduceOp> reductions() const { return reductions_; }

  const Memberships &memberships() const { return memberships_; }
  const llvm::StringMap<std::pair<int64_t, int64_t>> &bodySpans() const {
    return bodySpans_;
  }
  llvm::ArrayRef<mlir::Operation *>
  membershipOccurrences(llvm::StringRef instance, llvm::StringRef role,
                        int64_t occurrence) const;

private:
  Memberships memberships_;
  llvm::StringMap<std::pair<int64_t, int64_t>> bodySpans_;
  llvm::SmallVector<pir::ReduceOp> reductions_;
};

} // namespace zkc::semantics

#endif // ZKC_SEMANTICS_PROTOCOLFACTS_H
