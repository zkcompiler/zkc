//===- PirCompilerProvider.h - exact PIR compiler providers ----*- C++ -*-===//
//
// Representation-specific compiler providers for admitted PIR artifacts.
// This layer owns the exact environment required by the compiler and
// implements the first nonidentity transform family. The artifact-neutral
// CompilerCore remains independent of PIR and KZG.
//
//===----------------------------------------------------------------------===//
#ifndef ZKC_COMPILER_PIRCOMPILERPROVIDER_H
#define ZKC_COMPILER_PIRCOMPILERPROVIDER_H

#include "zkc/Artifact/Artifact.h"
#include "zkc/Compiler/CompilerCore.h"
#include "zkc/Registry/ProtocolEnvironment.h"

#include <memory>

namespace zkc::compiler {

/// Stable implementation revisions.  Provider instances retain these ids but
/// derive their exact source revisions from the semantic configuration they
/// own; callers should use `exactRef()` on the instance for dispatch.
const ExactRef &pirArtifactSemanticsV1Ref();
const ExactRef &pirSealedPayloadV1Ref();
const ExactRef &samePointKzgBatchV1Ref();
const ExactRef &samePointKzgBatchDomainV1Ref();

llvm::StringRef samePointKzgBatchSpaceParameter();
llvm::StringRef samePointKzgBatchOutputRole();
llvm::StringRef transformSurvivorOutputRole();

/// Immutable adapter payload. The admitted capability is the sole
/// representation-specific authority retained by the generic compiler
/// artifact.
class PirArtifactPayload {
public:
  PirArtifactPayload(const PirArtifactPayload &) = default;
  PirArtifactPayload(PirArtifactPayload &&) = default;
  PirArtifactPayload &operator=(const PirArtifactPayload &) = default;
  PirArtifactPayload &operator=(PirArtifactPayload &&) = default;

  const artifact::AdmittedPirArtifact &artifact() const { return artifact_; }

private:
  explicit PirArtifactPayload(artifact::AdmittedPirArtifact artifact)
      : artifact_(std::move(artifact)) {}

  artifact::AdmittedPirArtifact artifact_;

  friend class PirArtifactSemantics;
};

/// Exact authentication authority for the PIR representation.
///
/// The provider admits only capabilities minted by its complete compiler
/// environment. Representation-specific consumers clone through that
/// capability; the provider owns no parallel MLIR storage.
class PirArtifactSemantics final : public ArtifactSemantics {
public:
  explicit PirArtifactSemantics(registry::ProtocolEnvironment environment);

  const registry::ProtocolEnvironment &environment() const {
    return environment_;
  }

  const ExactRef &exactRef() const override { return ref_; }
  const ExactRef &payloadTypeRef() const override {
    return pirSealedPayloadV1Ref();
  }

  llvm::Expected<AuthenticatedArtifactObservation>
  authenticate(const ArtifactPayload &payload) const override;

  /// Wrap one already-admitted PIR capability. Its complete compiler
  /// environment must equal this provider's environment.
  llvm::Expected<ArtifactHandle>
  createArtifact(artifact::AdmittedPirArtifact artifact) const;

private:
  registry::ProtocolEnvironment environment_;
  ExactRef ref_;

  friend class SamePointKzgBatchTransformFamily;
  friend class SamePointKzgBatchTransformDomainProvider;
};

/// Generic same-point KZG batch transform.  The family recognizes one exact
/// canonical discovered group, realizes it in a clone, reseals through exact
/// registries, replay-checks the result, and returns checked merge/survivor
/// correspondences.  It selects no theorem: security is derived after the
/// seal, about the artifact this produced.
class SamePointKzgBatchTransformFamily final : public TransformFamily {
public:
  explicit SamePointKzgBatchTransformFamily(
      std::shared_ptr<const PirArtifactSemantics> semantics);

  const ExactRef &exactRef() const override { return ref_; }
  const ExactRef &artifactSemanticsRef() const override {
    return artifactSemanticsRef_;
  }

  llvm::Expected<CanonicalTransformApplication>
  recognize(AuthenticatedArtifactHandle before,
            const TransformApplication &requested) const override;
  llvm::Expected<ArtifactHandle>
  realize(AuthenticatedArtifactHandle before,
          const CanonicalTransformApplication &canonical) const override;
  llvm::Expected<std::vector<ClaimCorrespondence>>
  check(AuthenticatedArtifactHandle before, AuthenticatedArtifactHandle after,
        const CanonicalTransformApplication &canonical,
        uint64_t applicationIndex) const override;

private:
  std::shared_ptr<const PirArtifactSemantics> semantics_;
  ExactRef artifactSemanticsRef_;
  ExactRef ref_;
};

/// Complete finite domain over all pairwise-disjoint discovered maximal
/// groups.  Enumeration is identity followed by combinations in increasing
/// application count and lexicographic discovered-group order.
class SamePointKzgBatchTransformDomainProvider final
    : public TransformDomainProvider {
public:
  SamePointKzgBatchTransformDomainProvider(
      std::shared_ptr<const PirArtifactSemantics> semantics,
      registry::Rational batchSpace);

  const ExactRef &exactRef() const override { return ref_; }
  const ExactRef &artifactSemanticsRef() const override {
    return artifactSemanticsRef_;
  }

  llvm::Expected<std::vector<TransformPlan>>
  enumerate(const CompilerRequest &request,
            const AuthenticatedCompilerArtifact &source) const override;
  llvm::Expected<bool> contains(const CompilerRequest &request,
                                const AuthenticatedCompilerArtifact &source,
                                const TransformPlan &plan) const override;

private:
  std::shared_ptr<const PirArtifactSemantics> semantics_;
  ExactRef artifactSemanticsRef_;
  registry::Rational batchSpace_;
  ExactRef ref_;
};

} // namespace zkc::compiler

#endif // ZKC_COMPILER_PIRCOMPILERPROVIDER_H
