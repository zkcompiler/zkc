//===- CompilerCore.h - Closed compiler selection semantics -----*- C++ -*-===//
//
// A small, artifact-neutral compiler core.  The core owns no MLIR operation,
// registry handle, evidence object, certificate, serializer, or release
// policy. An adapter supplies one owned semantic artifact; the public service
// compiles it through checked search and independently checks the resulting
// decision.
//
//===----------------------------------------------------------------------===//
#ifndef ZKC_COMPILER_COMPILERCORE_H
#define ZKC_COMPILER_COMPILERCORE_H

#include "zkc/Soundness/SoundnessEvaluator.h"
#include "llvm/Support/Error.h"

#include <cstdint>
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

namespace zkc::compiler {

using soundness::ExactRef;

/// Immutable, no-RTTI payload seam for representation adapters.  The exact
/// payload reference names the adapter-owned semantic type; the template key
/// prevents a consumer from retrieving it as a different C++ type.
class ArtifactPayload {
public:
  virtual ~ArtifactPayload() = default;
  virtual const ExactRef &exactTypeRef() const = 0;
  virtual const void *get(const void *typeKey) const = 0;
};

namespace detail {
template <typename T> const void *artifactPayloadTypeKey() {
  static const char key = 0;
  return &key;
}

template <typename T>
class TypedArtifactPayload final : public ArtifactPayload {
public:
  TypedArtifactPayload(ExactRef typeRef, T value)
      : typeRef_(std::move(typeRef)), value_(std::move(value)) {}

  const ExactRef &exactTypeRef() const override { return typeRef_; }
  const void *get(const void *typeKey) const override {
    return typeKey == artifactPayloadTypeKey<T>() ? &value_ : nullptr;
  }

private:
  const ExactRef typeRef_;
  const T value_;
};
} // namespace detail

template <typename T>
std::shared_ptr<const ArtifactPayload> makeArtifactPayload(ExactRef typeRef,
                                                           T value) {
  return std::make_shared<const detail::TypedArtifactPayload<T>>(
      std::move(typeRef), std::move(value));
}

template <typename T>
const T *artifactPayloadAs(const ArtifactPayload &payload) {
  return static_cast<const T *>(
      payload.get(detail::artifactPayloadTypeKey<T>()));
}

struct VerifierProofRead {
  std::string payloadClass;
  ExactRef codecRef;
  uint64_t count = 1;
};

/// Semantic observations reconstructed by an exact representation adapter.
/// These values are derived from the immutable payload and have no
/// producer-populated mirror on OwnedCompilerArtifact.
struct AuthenticatedArtifactObservation {
  std::string artifactId;
  soundness::SealedSoundnessView soundness;
  std::vector<VerifierProofRead> verifierProofReads;
};

/// Raw semantic input to the compiler core.  A producer supplies only one
/// immutable representation payload and the exact authority that interprets
/// it.  Observations are not producer-populated mirrors: AUTHENTICATE derives
/// them once from this payload.
struct OwnedCompilerArtifact {
  OwnedCompilerArtifact(ExactRef artifactSemanticsRef,
                        std::shared_ptr<const ArtifactPayload> adapterPayload)
      : artifactSemanticsRef(std::move(artifactSemanticsRef)),
        adapterPayload(std::move(adapterPayload)) {}

  const ExactRef artifactSemanticsRef;
  const std::shared_ptr<const ArtifactPayload> adapterPayload;
};

using ArtifactHandle = std::shared_ptr<const OwnedCompilerArtifact>;

class AuthenticatedCompilerArtifact;
using AuthenticatedArtifactHandle =
    std::shared_ptr<const AuthenticatedCompilerArtifact>;

/// Representation-neutral authority for final seal and objective inputs.
///
/// A concrete adapter owns whatever exact registries or semantic environment
/// its payload representation requires.  The generic compiler sees only the
/// exact provider and payload type references plus reconstructed observations.
class ArtifactSemantics {
public:
  virtual ~ArtifactSemantics() = default;
  virtual const ExactRef &exactRef() const = 0;
  virtual const ExactRef &payloadTypeRef() const = 0;
  virtual llvm::Expected<AuthenticatedArtifactObservation>
  authenticate(const ArtifactPayload &payload) const = 0;

  /// Apply this exact authority to one raw artifact and mint an immutable
  /// authenticated capability.  Callers cannot provide the observation.
  llvm::Expected<AuthenticatedArtifactHandle>
  authenticateArtifact(ArtifactHandle artifact) const;
};

/// Core-owned result of applying one exact ArtifactSemantics authority to one
/// raw artifact.  Transform and derivation providers consume this type, so
/// payload-derived observations cannot be confused with producer assertions.
class AuthenticatedCompilerArtifact {
public:
  AuthenticatedCompilerArtifact(const AuthenticatedCompilerArtifact &) = delete;
  AuthenticatedCompilerArtifact &
  operator=(const AuthenticatedCompilerArtifact &) = delete;

  const ArtifactHandle artifact;
  const AuthenticatedArtifactObservation observation;

private:
  AuthenticatedCompilerArtifact(ArtifactHandle artifact,
                                AuthenticatedArtifactObservation observation)
      : artifact(std::move(artifact)), observation(std::move(observation)) {}

  friend class ArtifactSemantics;
};

struct TransformApplication {
  ExactRef familyRef;
  std::vector<soundness::ClaimRef> matchedClaims;
  std::map<std::string, soundness::ExactScalarValue, std::less<>> parameters;
};

struct CanonicalTransformApplication {
  ExactRef familyRef;
  std::vector<soundness::ClaimRef> orderedConsumed;
  std::map<std::string, soundness::ExactScalarValue, std::less<>> parameters;
};

struct TransformPlan {
  std::vector<TransformApplication> applications;
};

enum class TargetSelectorKind {
  FinalFrontier,
  TransformOutputs,
};

struct TargetSelector {
  TargetSelectorKind kind = TargetSelectorKind::FinalFrontier;
  ExactRef familyRef;
  std::string outputRole;
};

struct RequestedTarget {
  std::string key;
  std::vector<soundness::ClaimRef> orderedSourceClaims;
  TargetSelector selector;
  std::vector<std::string> admittedSchemaKeys;
};

struct TargetSchema {
  std::string key;
  soundness::SecurityIndex index;
  std::vector<soundness::TypedDeclaration> resources;
};

struct CompilerTargetPlan {
  std::string targetKey;
  /// Empty exactly when target resolution is empty.
  std::optional<std::string> schemaKey;
  /// Plans are stored in the canonical resolved-subject order.  REALIZE
  /// recomputes those subjects from checked lineage rather than duplicating
  /// them in the plan.
  std::vector<soundness::DerivationPlan> derivations;
};

struct CompilerPlan {
  TransformPlan transform;
  std::vector<CompilerTargetPlan> targets;
};

enum class ComparisonScopeKind {
  ClosedDomain,
  SubmittedFrontier,
};

struct ClosedDomainScope {};

struct SubmittedFrontierScope {
  std::vector<CompilerPlan> plans;
};

using ComparisonScope = std::variant<ClosedDomainScope, SubmittedFrontierScope>;

struct DerivationSurface {
  std::vector<ExactRef> allowedBindingRefs;
  std::vector<soundness::PrimitiveGameInstance> allowedPrimitiveGames;
  /// Exact caller-authorized external propositions.  AssumedJudgmentHolds is
  /// not a request-surface value: DERIVE creates it only for an explicit
  /// ExternalJudgmentAssumption leaf.
  std::vector<soundness::PropositionInstance> allowedHypotheses;
};

enum class BoundProjectionKind {
  ExtractionFailure,
  Scalar,
  Round,
  RoundMaximum,
};

struct BoundProjection {
  BoundProjectionKind kind = BoundProjectionKind::Scalar;
  /// Present exactly for Round.
  std::string exactRoundIndex;
};

struct ComparisonDomain {
  std::vector<soundness::TypedDeclaration> resources;
};

/// A total map from one result/schema resource domain into the enclosing
/// comparison domain.
using ResourceSubstitution =
    std::map<std::string, soundness::ClosedQuantity, std::less<>>;
using SchemaResourceSubstitutions =
    std::map<std::string, ResourceSubstitution, std::less<>>;

struct ExactTargetMember {
  uint64_t ordinal = 0;
};

enum class TargetFoldKind {
  Add,
  Max,
};

struct FoldTargetMembers {
  TargetFoldKind aggregate = TargetFoldKind::Add;
};

using TargetMemberSelector = std::variant<ExactTargetMember, FoldTargetMembers>;

struct CandidateTargetRead {
  std::string targetKey;
  TargetMemberSelector members = ExactTargetMember();
  BoundProjection projection;
  SchemaResourceSubstitutions resourceSubstitutions;
};

struct SourceMemberOf {
  std::string targetKey;
  soundness::ClaimRef exactSourceClaimRef;
};

struct SourceProjection {
  soundness::DerivationTarget sourceTarget;
  soundness::DerivationPlan sourceDerivationPlan;
  BoundProjection projection;
  ResourceSubstitution resourceSubstitution;
  SourceMemberOf targetRelation;
};

struct ZeroBound {};

struct BoundExpr;
using BoundExprPtr = std::shared_ptr<const BoundExpr>;

struct AddBounds {
  std::vector<BoundExprPtr> operands;
};

struct MaxBounds {
  std::vector<BoundExprPtr> operands;
};

struct ScaleBound {
  soundness::ClosedQuantity scale;
  BoundExprPtr operand;
};

/// One closed algebra used in two checked modes:
/// - candidate expressions admit CandidateTargetRead leaves;
/// - baseline expressions admit ZeroBound and SourceProjection leaves.
/// Add, Max, and Scale are shared, so comparison arithmetic has one syntax and
/// one evaluator rather than parallel candidate/baseline calculi.
struct BoundExpr {
  using Payload = std::variant<ZeroBound, CandidateTargetRead, SourceProjection,
                               AddBounds, MaxBounds, ScaleBound>;
  Payload payload = ZeroBound();
};

/// A total ceiling is exactly this relation with a ZeroBound baseline.
/// A nonzero source baseline expresses the relational introduced-loss form:
/// candidate <= baseline + ceiling.
struct SoundnessConstraint {
  ComparisonDomain comparisonDomain;
  BoundExpr candidate;
  BoundExpr baseline;
  soundness::ClosedBound ceiling;
};

enum class ObjectiveKind {
  StaticProofBytes,
  Unsupported,
};

enum class ObjectiveDirection {
  Minimize,
  Maximize,
};

struct Objective {
  std::string key;
  ObjectiveKind kind = ObjectiveKind::StaticProofBytes;
  ObjectiveDirection direction = ObjectiveDirection::Minimize;
  ExactRef codecWidthProfileRef;
};

struct CompilerLimits {
  uint64_t maxTransformApplications = 64;
  uint64_t maxTargets = 64;
  uint64_t maxDerivationNodes = 4096;
  uint64_t maxDerivationDepth = 256;
  uint64_t maxAlternativesPerSubject = 256;
  uint64_t maxDomainPlans = 65536;
};

struct CompilerRequest {
  ArtifactHandle source;
  ExactRef transformDomainProviderRef;
  ExactRef derivationPlanProviderRef;
  std::vector<RequestedTarget> targets;
  std::vector<TargetSchema> targetSchemas;
  DerivationSurface derivationSurface;
  std::vector<SoundnessConstraint> soundnessConstraints;
  std::vector<Objective> objectives;
  ComparisonScope comparisonScope = ClosedDomainScope();
  CompilerLimits limits;
};

class TransformDomainProvider {
public:
  virtual ~TransformDomainProvider() = default;
  virtual const ExactRef &exactRef() const = 0;
  virtual const ExactRef &artifactSemanticsRef() const = 0;
  virtual llvm::Expected<std::vector<TransformPlan>>
  enumerate(const CompilerRequest &request,
            const AuthenticatedCompilerArtifact &source) const = 0;
  virtual llvm::Expected<bool>
  contains(const CompilerRequest &request,
           const AuthenticatedCompilerArtifact &source,
           const TransformPlan &plan) const = 0;
};

struct ProducedClaim {
  soundness::ClaimRef claim;
  std::string outputRole;
};

/// One whole transform application, not a set of pairwise edges.  This shape
/// preserves many-to-one and one-to-many lineage without inventing synthetic
/// claim correspondences.
struct ClaimCorrespondence {
  uint64_t applicationIndex = 0;
  ExactRef familyRef;
  std::vector<soundness::ClaimRef> orderedConsumed;
  std::vector<ProducedClaim> orderedProduced;
};

/// A property a transform family asserts its application preserves.
///
/// `LEGAL` never reads one. A family that preserves a property does so by an
/// argument this judgment does not contain (spec/compiler.md §7.2), so naming
/// the property is how that argument becomes findable rather than folklore: a
/// consumer holding a claim has been told whose argument to go and read, not
/// told that the property holds.
///
/// `propertyRef` is an open identifier on purpose. What this fixes is the
/// placement: a preservation claim has a stable carrier slot rather than being
/// added later as an unrelated witness-format extension. Which properties can
/// be claimed, and what a claim about one is conditional on, are decided by the
/// completeness and zero-knowledge programs when they run; committing an
/// enumeration here would settle their vocabulary from a place that has not
/// done their work.
///
/// The family reference carries its revision, so a claim is pinned to the
/// version of the family that made it.
struct PreservationClaim {
  std::string propertyRef;
  ExactRef familyRef;
  uint64_t applicationIndex = 0;
};

bool operator==(const PreservationClaim &lhs, const PreservationClaim &rhs);

/// Typed, immutable transform semantics for executable nonidentity
/// realization.
/// Recognition, realization, and checking are distinct judgments.
/// Implementations receive and return owned artifact handles; no ambient
/// callback or mutable IR handle enters a realization trace.
class TransformFamily {
public:
  virtual ~TransformFamily() = default;
  virtual const ExactRef &exactRef() const = 0;
  virtual const ExactRef &artifactSemanticsRef() const = 0;
  virtual llvm::Expected<CanonicalTransformApplication>
  recognize(AuthenticatedArtifactHandle before,
            const TransformApplication &requested) const = 0;
  virtual llvm::Expected<ArtifactHandle>
  realize(AuthenticatedArtifactHandle before,
          const CanonicalTransformApplication &canonical) const = 0;
  virtual llvm::Expected<std::vector<ClaimCorrespondence>>
  check(AuthenticatedArtifactHandle before, AuthenticatedArtifactHandle after,
        const CanonicalTransformApplication &canonical,
        uint64_t applicationIndex) const = 0;

  /// What this application claims to preserve beyond the transition and the
  /// bound.  Claiming nothing is the default and is the honest state for a
  /// family whose argument for a property nobody has written down: a consumer
  /// then knows to obtain the property elsewhere rather than assuming it.
  ///
  /// Nothing here is checked, so a claim cannot make an illegal transform
  /// legal and cannot make a legal one more so.  It is a record of who is on
  /// the hook.
  virtual std::vector<PreservationClaim>
  preservationClaims(AuthenticatedArtifactHandle before,
                     AuthenticatedArtifactHandle after,
                     const CanonicalTransformApplication &canonical,
                     uint64_t applicationIndex) const {
    (void)before;
    (void)after;
    (void)canonical;
    (void)applicationIndex;
    return {};
  }
};

/// Minimal closed transform domain containing only the empty identity plan.
class IdentityTransformDomainProvider final : public TransformDomainProvider {
public:
  IdentityTransformDomainProvider(ExactRef ref, ExactRef artifactSemanticsRef);

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
  ExactRef ref_;
  ExactRef artifactSemanticsRef_;
};

struct ListedDerivationAlternative {
  std::string targetKey;
  std::string schemaKey;
  soundness::SecuritySubject subject;
  soundness::DerivationPlan plan;
};

class DerivationPlanDomainProvider {
public:
  virtual ~DerivationPlanDomainProvider() = default;
  virtual const ExactRef &exactRef() const = 0;
  virtual llvm::Expected<std::vector<soundness::DerivationPlan>>
  enumerate(const CompilerRequest &request,
            const AuthenticatedCompilerArtifact &artifact,
            const RequestedTarget &target, const TargetSchema &schema,
            const soundness::SecuritySubject &subject) const = 0;
  virtual llvm::Expected<bool>
  contains(const CompilerRequest &request,
           const AuthenticatedCompilerArtifact &artifact,
           const RequestedTarget &target, const TargetSchema &schema,
           const soundness::SecuritySubject &subject,
           const soundness::DerivationPlan &plan) const = 0;
};

/// A finite, explicitly ordered set of derivation alternatives.  Enumeration
/// order is semantic and participates in the final domain-ordinal tie-break.
class ListedDerivationPlanDomainProvider final
    : public DerivationPlanDomainProvider {
public:
  ListedDerivationPlanDomainProvider(
      ExactRef ref, std::vector<ListedDerivationAlternative> alternatives);

  const ExactRef &exactRef() const override { return ref_; }
  llvm::Expected<std::vector<soundness::DerivationPlan>>
  enumerate(const CompilerRequest &request,
            const AuthenticatedCompilerArtifact &artifact,
            const RequestedTarget &target, const TargetSchema &schema,
            const soundness::SecuritySubject &subject) const override;
  llvm::Expected<bool>
  contains(const CompilerRequest &request,
           const AuthenticatedCompilerArtifact &artifact,
           const RequestedTarget &target, const TargetSchema &schema,
           const soundness::SecuritySubject &subject,
           const soundness::DerivationPlan &plan) const override;

private:
  ExactRef ref_;
  std::vector<ListedDerivationAlternative> alternatives_;
};

struct CodecWidth {
  ExactRef codecRef;
  registry::Rational byteWidth;
};

struct CodecWidthProfile {
  ExactRef ref;
  std::map<std::string, CodecWidth, std::less<>> codecs;
};

struct CompilerSemanticContext {
  std::shared_ptr<const soundness::SoundnessContext> soundnessContext;
  std::map<std::string, std::shared_ptr<const ArtifactSemantics>, std::less<>>
      artifactSemantics;
  std::map<std::string, std::shared_ptr<const TransformDomainProvider>,
           std::less<>>
      transformDomains;
  std::map<std::string, std::shared_ptr<const TransformFamily>, std::less<>>
      transformFamilies;
  std::map<std::string, std::shared_ptr<const DerivationPlanDomainProvider>,
           std::less<>>
      derivationDomains;
  std::map<std::string, CodecWidthProfile, std::less<>> codecWidthProfiles;
};

struct CompilerResult {
  std::optional<uint64_t> selectedOrdinal;
};

struct DecisionVerdict {
  bool accepted = false;
  std::string detail;
};

/// Checked compilation computes DOMAIN, REALIZE, VALID, SCORE, and SELECT from
/// the request rather than accepting producer-authored stage results.
llvm::Expected<CompilerResult> compile(const CompilerSemanticContext &context,
                                       const CompilerRequest &request);

/// Decision checking performs a fresh checked compilation and compares only
/// the submitted decision record with that independent recomputation.
llvm::Expected<DecisionVerdict>
checkDecision(const CompilerSemanticContext &context,
              const CompilerRequest &request, const CompilerResult &submitted);

} // namespace zkc::compiler

#endif // ZKC_COMPILER_COMPILERCORE_H
