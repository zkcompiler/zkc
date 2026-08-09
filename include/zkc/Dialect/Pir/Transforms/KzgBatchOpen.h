//===- KzgBatchOpen.h - exact same-point KZG batch core --------*- C++ -*-===//
//
// Reusable, pass-independent mechanics for the first non-identity PIR
// transform family.  The API names one exact canonical source-claim group,
// realizes only that group, and checks a claimed result by deterministic
// replay.  It owns no compiler policy, theorem choice, certificate, evidence,
// or pass-manifest semantics.
//
//===----------------------------------------------------------------------===//
#ifndef ZKC_DIALECT_PIR_TRANSFORMS_KZGBATCHOPEN_H
#define ZKC_DIALECT_PIR_TRANSFORMS_KZGBATCHOPEN_H

#include "zkc/Dialect/Pir/PirOps.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"

#include <cstdint>
#include <string>
#include <vector>

namespace zkc::pir {

/// Exact identity of one consumed claim occurrence in the source protocol.
/// Both fields come from the PIR canonical index.  The digest identifies
/// the complete descriptor; the index distinguishes equal descriptor
/// occurrences (which this transform conservatively refuses within a group).
struct KzgBatchOpenClaimRef {
  uint64_t claimIndex = 0;
  std::string descriptorDigest;
};

bool operator==(const KzgBatchOpenClaimRef &left,
                const KzgBatchOpenClaimRef &right);

/// One canonical maximal same-point application.  `orderedClaims` follows the
/// transform's canonical complete-descriptor order, never source visitation
/// order.  `membersAnchor` is the exact MaterialExpr result used by the
/// admitted `kzg_batch` reduction contract.
struct KzgBatchOpenApplication {
  std::string pointAnchor;
  std::string membersAnchor;
  std::vector<KzgBatchOpenClaimRef> orderedClaims;
};

bool operator==(const KzgBatchOpenApplication &left,
                const KzgBatchOpenApplication &right);

/// Discover every exact eligible maximal group, ordered by point anchor.
/// Ineligible single-opening shapes are declined.  An ambiguous group
/// (including duplicate complete descriptors) is refused rather than
/// partially rewritten.
llvm::Expected<std::vector<KzgBatchOpenApplication>>
discoverSamePointKzgBatchOpenApplications(ProtocolOp protocol);

/// Recognize one requested ordered claim vector as exactly one discovered
/// canonical application.  Reordering, subsets, supersets, and unknown claims
/// refuse.
llvm::Expected<KzgBatchOpenApplication>
recognizeSamePointKzgBatchOpenApplication(
    ProtocolOp protocol, llvm::ArrayRef<KzgBatchOpenClaimRef> orderedClaims);

/// Realize exactly `application` in the supplied owned open protocol.
/// All recognition and derived-anchor work completes before mutation.  This
/// function makes no security claim.
llvm::Expected<ReduceOp> realizeSamePointKzgBatchOpenApplication(
    ProtocolOp protocol, const KzgBatchOpenApplication &application,
    llvm::StringRef batchChallengeSpace);

/// Check a claimed result by cloning `before`, replaying the one exact
/// application, and comparing the resulting semantic IR to `after`.
/// Locations and discardable attributes are outside this judgment.
llvm::Expected<bool> checkSamePointKzgBatchOpenApplication(
    ProtocolOp before, ProtocolOp after,
    const KzgBatchOpenApplication &application,
    llvm::StringRef batchChallengeSpace);

} // namespace zkc::pir

#endif // ZKC_DIALECT_PIR_TRANSFORMS_KZGBATCHOPEN_H
