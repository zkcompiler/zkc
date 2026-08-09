//===- CanonicalEncoder.h - Canonical protocol encoding ---------*- C++ -*-===//
#ifndef ZKC_ENCODING_CANONICALENCODER_H
#define ZKC_ENCODING_CANONICALENCODER_H

#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/IR/Value.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"

#include <cstdint>
#include <optional>
#include <string>

namespace zkc {
namespace encoding {

/// The canonical encoding of a protocol container (docs/spec/kernel.md
/// §8, carrier.md §6): a deterministic JSON byte string over exactly the
/// kernel identity set — policy, construction profile, claims, ordered
/// spine events with position-encoded references, semantic material bindings,
/// and terminal sinks.
/// The walk reads the single flat body form; derived tables never participate.
/// The reference twin is `reference/oracle` and byte parity with it is
/// the acceptance gate for any change here.
llvm::Expected<std::string> encodeCanonical(mlir::Operation *container);

/// SHA-256 of the canonical encoding, as 64 lowercase hex digits — the
/// artifact identity. One identity, one spelling.
llvm::Expected<std::string> computeId(mlir::Operation *container);

/// Authenticate one stored PIR sealed-artifact identity at a consumer
/// boundary. This is deliberately separate from computeId: seal and raw id
/// translation mint a value from canonical content, while consumers refuse a
/// stored value that does not name that content.
llvm::Error validatePirIdentity(mlir::Operation *container);

/// The canonical position spaces of one container — the same three
/// numberings the canonical encoding writes (event ≤ order, claim production
/// order over the normalized transformer sequence, transformer
/// position) — plus each claim's **descriptor digest**: the
/// content-derived claim reference, `SHA256("zkc/claim\n" ‖
/// canonical([profile, anchors]))` in `sha256:<hex>` reference form —
/// deliberately position-free, so a transform's multiset
/// correspondence survives event insertion; the position rides beside
/// it as `claim_index`. Derived by the same walk that computes the
/// identity, so a position here is exactly a position in the sealed
/// encoding.
struct CanonicalIndex {
  /// Every canonical event operation to its event position. This is the
  /// operation-level authority used by projection and composition; the two
  /// maps below retain the value/check views needed by identity consumers.
  llvm::DenseMap<mlir::Operation *, int64_t> eventOperationPositions;
  llvm::DenseMap<mlir::Value, int64_t> eventPositions;
  llvm::DenseMap<mlir::Operation *, int64_t> checkPositions;
  llvm::DenseMap<mlir::Operation *, int64_t> transformerPositions;
  llvm::DenseMap<mlir::Value, int64_t> claimPositions;
  llvm::DenseMap<mlir::Value, std::string> claimDescriptors;
};

/// Build the event-position portion of the canonical index directly from a
/// container body. This is the event walk used by the full encoder, and is
/// available before sealing so open-protocol composition uses the same event
/// authority without pretending the container already has an identity.
CanonicalIndex canonicalEventIndex(mlir::Block &body);

/// Look up one operation in the canonical event space. Non-events have no
/// position.
std::optional<int64_t> canonicalEventPosition(const CanonicalIndex &index,
                                              mlir::Operation *operation);

/// Number of events represented by a canonical index.
int64_t canonicalEventCount(const CanonicalIndex &index);

llvm::Expected<CanonicalIndex> canonicalIndex(mlir::Operation *container);

/// The key the canonical encoding orders source claims by: the claim profile,
/// a NUL, then the canonical anchor bytes. Claim positions are what "claim 0"
/// means, and a second implementation of this order is a second answer to that
/// question — one that downstream code compares against this one for equality.
/// Exported so there is only ever one answer.
llvm::Expected<std::string>
canonicalSourceClaimKey(llvm::StringRef profile,
                        const llvm::json::Value &anchors);

/// The canonical claim descriptor, `[profile, anchors]` — the preimage the
/// claim reference digests and the value every consumer compares claims by.
/// Exported for the same reason the source-claim order is: it was built from
/// scratch in four places, and two of the copies disagreed about whether a
/// canonicalization failure is an error or a claim that quietly does not
/// exist.
llvm::Expected<llvm::json::Value>
canonicalClaimDescriptor(llvm::StringRef profile, mlir::DictionaryAttr anchors);

/// The canonical encoding of an OIR artifact: endpoint kind, source
/// citation, ABI labels, and the program rows in block order with
/// operand references as ["a", argNo] / ["r", opIdx, resultNo] and
/// provenance as position arrays. The stored id is excluded (it is the
/// hash OF this encoding). reference/oracle's project() computes the
/// same bytes.
llvm::Expected<std::string> encodeOirCanonical(mlir::Operation *artifact);

/// SHA-256 of the OIR canonical encoding, 64 lowercase hex digits.
llvm::Expected<std::string> computeOirId(mlir::Operation *artifact);

/// The provenance-independent endpoint semantic identity (carrier.md §6.1):
/// SHA-256 under "zkc/oir-semantic\n" of the canonical document with the
/// PIR source citation dropped and every row's src position list erased.
/// Two artifacts that differ only in projection provenance have equal
/// semantic ids; it is a computable view, never a second stored field.
llvm::Expected<std::string> computeOirSemanticId(mlir::Operation *artifact);

/// Authenticate one stored OIR artifact identity at a consumer boundary.
/// This recomputes the canonical id and refuses when it differs from the
/// authored `oir.artifact` id.  Minting tools intentionally call
/// computeOirId directly; consumers must call this check before deriving a
/// view or executing the endpoint.
llvm::Error validateOirIdentity(mlir::Operation *artifact);

} // namespace encoding
} // namespace zkc

#endif // ZKC_ENCODING_CANONICALENCODER_H
