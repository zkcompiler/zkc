//===- Projection.h - admitted PIR endpoint projection ---------*- C++ -*-===//
#ifndef ZKC_DIALECT_PIR_TRANSFORMS_PROJECTION_H
#define ZKC_DIALECT_PIR_TRANSFORMS_PROJECTION_H

#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"

#include <memory>
#include <utility>

namespace zkc::artifact {
class AdmittedPirArtifact;
} // namespace zkc::artifact

namespace zkc::oir {
class ArtifactOp;
} // namespace zkc::oir

namespace zkc::registry {
class ProtocolEnvironment;
} // namespace zkc::registry

namespace zkc::pir {

/// The endpoint kinds with implemented projection semantics.
enum class EndpointKind { Verifier, ProverSkeleton };

llvm::Expected<EndpointKind> parseEndpointKind(llvm::StringRef spelling);
llvm::StringRef endpointKindName(EndpointKind kind);

/// One immutable OIR image projected from an admitted PIR artifact. The
/// backing context and the raw PIR clone remain private and live as long as
/// this copyable result.
class ProjectedOirArtifact {
public:
  // Intentionally copy-only: a destructive move would leave a still-callable
  // capability object whose storage is gone, and a copy is one shared_ptr
  // increment. Declaring the copy operations suppresses the implicit moves,
  // so an rvalue silently copies instead.
  ProjectedOirArtifact(const ProjectedOirArtifact &) = default;
  ProjectedOirArtifact &operator=(const ProjectedOirArtifact &) = default;

  llvm::StringRef id() const;
  EndpointKind endpointKind() const;
  void print(llvm::raw_ostream &os) const;

private:
  struct Storage;
  explicit ProjectedOirArtifact(std::shared_ptr<const Storage> storage)
      : storage_(std::move(storage)) {}

  std::shared_ptr<const Storage> storage_;

  friend llvm::Expected<ProjectedOirArtifact>
  projectArtifact(const artifact::AdmittedPirArtifact &, EndpointKind);
};

/// Project an already admitted immutable PIR subject. This boundary clones the
/// subject internally and performs the endpoint-specific realization and
/// COV_realized judgments. It does not repeat transport or seal admission.
llvm::Expected<ProjectedOirArtifact>
projectArtifact(const artifact::AdmittedPirArtifact &artifact,
                EndpointKind endpointKind);

/// Standalone OIR admission (docs/spec/endpoints.md §3): authenticates the
/// stored identity, then re-resolves every hole_call contract digest against
/// the environment and checks the complete declared ABI the executor will
/// dispatch on — kind, operand and result segments (sort, class, count,
/// order), and static parameter arity — and requires every counterparty
/// discharge kind to be a row of the closed table. An artifact citing an
/// unloaded or content-mismatched HoleContract refuses (zkc-E238).
llvm::Error admitOirArtifact(oir::ArtifactOp artifact,
                             const registry::ProtocolEnvironment &environment);

} // namespace zkc::pir

#endif // ZKC_DIALECT_PIR_TRANSFORMS_PROJECTION_H
