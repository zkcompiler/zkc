//===- Artifact.h - persisted PIR artifact lifecycle -----------*- C++ -*-===//
#ifndef ZKC_ARTIFACT_ARTIFACT_H
#define ZKC_ARTIFACT_ARTIFACT_H

#include "mlir/Support/LogicalResult.h"
#include "zkc/Dialect/Pir/PirOps.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"

#include <memory>
#include <string>
#include <utility>

namespace zkc::registry {
class ProtocolEnvironment;
} // namespace zkc::registry

namespace zkc::artifact {

class AdmittedPirArtifact;

namespace detail {
class ArtifactAccess;
} // namespace detail

/// The producer string stamped into every artifact this build writes:
/// the release, "zkc_v0" while zkc is at v0. The marker is error locality —
/// it names a foreign artifact clearly. Acceptance never rides on it:
/// the identity recheck and the dialect version blob are the gates.
std::string producerString();

/// Serializes one sealed protocol as a bytecode artifact; the sealed op
/// is the bytecode root — an artifact is exactly one `pir.sealed`
/// (docs/spec/carrier.md). The writer recomputes the canonical identity and
/// refuses a mismatch before emitting bytes; consumers independently repeat
/// the same check at load.
mlir::LogicalResult writeArtifact(pir::SealedOp sealed, llvm::raw_ostream &os);

/// A decoded PIR artifact.
///
/// Decoding authenticates the transport shape, producer, structural verifier,
/// and stored identity. It does not apply the registry-backed seal judgment.
/// Storage is shared, private, and never exposed through this interface.
class DecodedPirArtifact {
public:
  // Intentionally copy-only: a destructive move would leave a still-callable
  // capability object whose storage is gone, and a copy is one shared_ptr
  // increment. Declaring the copy operations suppresses the implicit moves,
  // so an rvalue silently copies instead.
  DecodedPirArtifact(const DecodedPirArtifact &) = default;
  DecodedPirArtifact &operator=(const DecodedPirArtifact &) = default;

  llvm::StringRef id() const;
  void print(llvm::raw_ostream &os) const;

private:
  struct Storage;
  explicit DecodedPirArtifact(std::shared_ptr<const Storage> storage)
      : storage_(std::move(storage)) {}

  std::shared_ptr<const Storage> storage_;

  friend class detail::ArtifactAccess;
  friend class AdmittedPirArtifact;
  friend llvm::Expected<DecodedPirArtifact> loadArtifact(llvm::StringRef,
                                                         llvm::StringRef);
  friend llvm::Expected<DecodedPirArtifact> snapshotArtifact(pir::SealedOp);
  friend llvm::Expected<AdmittedPirArtifact>
      admitArtifact(DecodedPirArtifact, registry::ProtocolEnvironment);
};

/// A decoded artifact admitted against one exact immutable protocol
/// environment. Copies retain the same immutable subject and authority.
///
/// The `const Storage` share does not itself freeze the IR — OwningOpRef
/// hands out the operation by value through a const accessor — so subject
/// immutability rests on this interface exposing no operation accessor.
/// Any future accessor must return a clone, never the stored operation.
class AdmittedPirArtifact {
public:
  // Intentionally copy-only: a destructive move would leave a still-callable
  // capability object whose moved-from storage was no longer authenticated,
  // and a copy is one shared_ptr increment. Declaring the copy operations
  // suppresses the implicit moves, so an rvalue silently copies instead.
  AdmittedPirArtifact(const AdmittedPirArtifact &) = default;
  AdmittedPirArtifact &operator=(const AdmittedPirArtifact &) = default;

  llvm::StringRef id() const;
  const registry::ProtocolEnvironment &environment() const;

private:
  struct Storage;
  explicit AdmittedPirArtifact(std::shared_ptr<const Storage> storage)
      : storage_(std::move(storage)) {}

  std::shared_ptr<const Storage> storage_;

  friend class detail::ArtifactAccess;
  friend llvm::Expected<AdmittedPirArtifact>
      admitArtifact(DecodedPirArtifact, registry::ProtocolEnvironment);
};

/// The fail-closed artifact loader (docs/spec/carrier.md). Checks,
/// in order: the file is MLIR bytecode with a well-formed header and a
/// zkc producer marker (zkc-E802) — which names a foreign writer
/// rather than negotiating a version, the content is
/// exactly one verifying `pir.sealed` (zkc-E803), and the identity
/// recomputed by the canonical encoder equals the stored id — and
/// `expectedId`, when the caller knows which artifact it wants
/// (zkc-E801). Anything unexpected rejects; nothing is repaired.
llvm::Expected<DecodedPirArtifact>
loadArtifact(llvm::StringRef path, llvm::StringRef expectedId = "");

/// Capture a sealed operation into independent decoded storage. The operation
/// is serialized through the same bytecode transport and decoded into a fresh
/// context; later source-context mutation cannot affect the snapshot.
llvm::Expected<DecodedPirArtifact> snapshotArtifact(pir::SealedOp sealed);

/// Apply the exact registry-backed seal judgment once and mint a reusable
/// immutable capability. The decoded input remains valid regardless of
/// whether the returned capability is copied, serialized, or cloned; those
/// later copies are raw input if they cross another semantic boundary.
llvm::Expected<AdmittedPirArtifact>
admitArtifact(DecodedPirArtifact decoded,
              registry::ProtocolEnvironment environment);

llvm::Expected<AdmittedPirArtifact>
loadAndAdmitArtifact(llvm::StringRef path,
                     registry::ProtocolEnvironment environment,
                     llvm::StringRef expectedId = "");

} // namespace zkc::artifact

#endif // ZKC_ARTIFACT_ARTIFACT_H
