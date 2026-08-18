//===- SealedSoundnessView.h - Owned sealed-subject view -------*- C++ -*-===//
//
// A minimal, MLIR-free view of the sealed facts needed to identify theorem
// application subjects.  The PIR adapter constructs this value from canonical
// identity positions and exact registry pins; consumers never retain an MLIR
// handle or registry pointer.
//
//===----------------------------------------------------------------------===//
#ifndef ZKC_SOUNDNESS_SEALEDSOUNDNESSVIEW_H
#define ZKC_SOUNDNESS_SEALEDSOUNDNESSVIEW_H

#include "zkc/Soundness/SoundnessKernel.h"
#include "llvm/Support/Error.h"

#include <cstdint>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <variant>
#include <vector>

namespace zkc::soundness {

/// One exact claim occurrence in an artifact.  The descriptor digest commits
/// to profile and anchors; the canonical index distinguishes equal
/// descriptors produced at different positions.
struct ClaimRef {
  uint64_t claimIndex = 0;
  std::string descriptorDigest;
};

bool operator==(const ClaimRef &lhs, const ClaimRef &rhs);
bool operator!=(const ClaimRef &lhs, const ClaimRef &rhs);

struct ProtocolClaimSubject {
  std::string artifactId;
  ClaimRef claim;
};

bool operator==(const ProtocolClaimSubject &lhs,
                const ProtocolClaimSubject &rhs);
bool operator!=(const ProtocolClaimSubject &lhs,
                const ProtocolClaimSubject &rhs);

struct ConsumedClaimVectorSubject {
  std::string artifactId;
  ClaimRef consumer;
  std::vector<ClaimRef> orderedSources;
};

bool operator==(const ConsumedClaimVectorSubject &lhs,
                const ConsumedClaimVectorSubject &rhs);
bool operator!=(const ConsumedClaimVectorSubject &lhs,
                const ConsumedClaimVectorSubject &rhs);

/// An exact reduction output occurrence.  `ownerClaim` is redundant by
/// design: resolution first selects the canonical transformer and output,
/// then requires the resolved output to equal this complete claim reference.
struct ReductionOccurrence {
  std::string artifactId;
  ClaimRef ownerClaim;
  uint64_t transformerPosition = 0;
  uint64_t outputIndex = 0;
};

/// A path application site identifies only the exact artifact and claim
/// occurrence. APPLY supplies the binding and authorizes its path-transition
/// anchor.
struct PathOccurrence {
  std::string artifactId;
  ClaimRef claim;
};

using ApplicationSite = std::variant<ReductionOccurrence, PathOccurrence>;

enum class ChallengeShape { Scalar, Vector };
enum class ChallengeSampling { Uniform, UniformIndependent };

struct SealedMessageRoleFact {
  std::string role;
  std::vector<std::string> payloadClassesByOccurrence;
};

bool operator==(const SealedMessageRoleFact &lhs,
                const SealedMessageRoleFact &rhs);

/// One exact contract round reconstructed from the pinned contract and the
/// sealed event/member geometry.  Optional derived fields are present only
/// where their mathematical domain is exact.
struct SealedRoundFact {
  uint64_t position = 0;
  std::string kind;
  std::string challengeRole;
  uint64_t challengeEventPosition = 0;
  std::string challengePayloadClass;
  std::string challengeDomain;
  registry::Rational challengeSpace;
  uint64_t challengeCount = 1;
  ChallengeShape shape = ChallengeShape::Scalar;
  ChallengeSampling sampling = ChallengeSampling::Uniform;
  std::vector<SealedMessageRoleFact> messages;
  std::optional<registry::Rational> roundDegree;
  std::optional<registry::Rational> challengeSpaceLog2;
};

bool operator==(const SealedRoundFact &lhs, const SealedRoundFact &rhs);

/// Raw canonical parameter carriers copied from `pir.reduce.params`.  A
/// theorem projection performs the requested exact integer/rational parsing;
/// the adapter does not guess a theorem-level type from a protocol atom.
struct SealedParameterAtom {
  enum class Carrier { String, Integer, Boolean };

  Carrier carrier = Carrier::String;
  std::variant<std::string, registry::Rational, bool> value = std::string();
};

bool operator==(const SealedParameterAtom &lhs, const SealedParameterAtom &rhs);

/// Existence of this value is the authenticated grinding relation.  It carries
/// exact canonical positions instead of caller-supplied truth flags.
struct RoundAdjacencyValue {
  ExactRef contractRef;
  uint64_t grindingTransformerPosition = 0;
  ClaimRef premiseClaim;
  uint64_t premiseTransformerPosition = 0;
  uint64_t powChallengeEventPosition = 0;
  uint64_t pinCheckEventPosition = 0;
  uint64_t successorChallengeEventPosition = 0;
  uint64_t premiseRoundPosition = 0;
};

bool operator==(const RoundAdjacencyValue &lhs, const RoundAdjacencyValue &rhs);

enum class CodecKind { ModReduce, TupleBijection };

struct SealedChallengeCodecFact {
  uint64_t eventPosition = 0;
  std::string payloadClass;
  std::string domain;
  registry::Rational space;
  uint64_t count = 1;
  ChallengeShape shape = ChallengeShape::Scalar;
  ChallengeSampling sampling = ChallengeSampling::Uniform;
  ExactRef codecRef;
  CodecKind codecKind = CodecKind::ModReduce;
  uint64_t squeezeSymbols = 0;
  registry::Rational biasContribution;
};

bool operator==(const SealedChallengeCodecFact &lhs,
                const SealedChallengeCodecFact &rhs);

/// Artifact-global construction facts used by a duplex path rule.  The exact
/// kappa/profile/challenge inputs are retained; path authorization is performed
/// by APPLY from its selected binding, because the artifact carries no
/// theorem citation of its own.
struct SealedDuplexFacts {
  ExactRef spongeRef;
  registry::Rational alphabetOrder;
  uint64_t capacity = 0;
  uint64_t rate = 0;
  std::string iv;
  std::vector<uint64_t> segmentStarts;
  std::vector<SealedChallengeCodecFact> challenges;
  registry::Rational codecBiasMax;
  registry::Rational codecBiasSum;
};

bool operator==(const SealedDuplexFacts &lhs, const SealedDuplexFacts &rhs);

/// The owned, theorem-independent reduction facts needed for occurrence and
/// consumed-subject resolution.  The exact contract reference authenticates
/// the structural protocol occurrence; a RuleBinding selected by APPLY
/// supplies theorem semantics separately.
struct SealedReduction {
  uint64_t transformerPosition = 0;
  ExactRef contractRef;
  std::vector<ClaimRef> orderedInputs;
  /// Descriptor anchors of each consumed claim, in the same order as
  /// `orderedInputs`.  The inner event-position map contains an entry only
  /// when that exact anchor value is tied by `pir.material_bind` to one
  /// canonical transcript event.  Missing entries remain explicit absence;
  /// theorem predicates that need them fail closed.
  std::vector<std::map<std::string, std::string, std::less<>>>
      orderedInputAnchors;
  std::vector<std::map<std::string, uint64_t, std::less<>>>
      orderedInputAnchorEventPositions;
  std::vector<ClaimRef> orderedOutputs;
  std::map<std::string, SealedParameterAtom, std::less<>> parameters;
  std::vector<SealedRoundFact> rounds;
  std::map<std::string, uint64_t, std::less<>> selectedCheckEventPositions;
  std::optional<RoundAdjacencyValue> roundAdjacency;
};

/// Claims are indexed by canonical claim position.  Reductions are keyed by
/// canonical transformer position, which is not a reduction ordinal.
struct SealedSoundnessView {
  std::string artifactId;
  std::vector<ClaimRef> claimsByIndex;
  /// Anchors of each claim, by canonical claim index, and the exact material
  /// references tied by `pir.material_bind` to a transcript position.
  /// Together they carry the grounded/declared distinction a witness reader
  /// needs: an anchor whose value appears among the bound references is
  /// grounded -- two artifacts agreeing on it agree about a runtime value --
  /// while a declared anchor records its authors' agreement.  Both are
  /// legitimate, and an entry claim's anchors are necessarily declared; the
  /// distinction is projected for visibility, never consulted by a judgment.
  std::vector<std::map<std::string, std::string, std::less<>>>
      claimAnchorsByIndex;
  std::set<std::string, std::less<>> boundMaterialRefs;
  /// The label of the value each semantic reference is bound to, where
  /// the bound value comes from a labelled spine event. A consumer
  /// relating an artifact's statement to an external object needs the
  /// label, not only the fact that some value was bound.
  std::map<std::string, std::string, std::less<>> boundMaterialLabels;
  /// The public statement ABI: instance-stage binding labels in spine
  /// order, which is the order an endpoint's arguments carry. Projected
  /// for consumers that relate the artifact's statement to an external
  /// object (docs/spec/relations.md §2.6); no judgment here reads it.
  std::vector<std::string> statementLabels;

  /// The values of seal-stage bindings, by label. A seal-stage binding
  /// carries its value in sealed content, so a consumer relating an
  /// artifact to an external object can check what the transcript
  /// carries rather than take it on the artifact's word
  /// (docs/spec/relations.md §2.8); no judgment here reads it.
  std::map<std::string, std::string, std::less<>> sealBindValues;
  std::map<uint64_t, SealedReduction> reductionsByTransformerPosition;
  std::optional<SealedDuplexFacts> duplex;

  /// The seal policy this artifact was sealed under. Every other field
  /// here is geometry a rule reads to price one step; this one is read
  /// by the artifact judgment, which asks whether a derivation covers
  /// the whole artifact rather than what a step costs. Projected rather
  /// than re-derived, because the seal battery already decided it and a
  /// second reading is a second chance to disagree.
  std::string policy;
};

/// One transformer's body extent and whether it commutes.
///
/// The extent is the transformer's membership events -- the messages its
/// contract's rounds declare -- in canonical positions. It deliberately does
/// not cover the challenges those rounds sample: a challenge reaches a
/// reduction as a dependency operand rather than as a member, and a
/// transformer may sample one inside another's block on purpose. Grinding is
/// exactly that shape, and the adjacency value the adapter builds is what
/// authenticates and prices the placement.
///
/// `central` is kernel.md §4's predicate: a transformer whose body contains
/// no absorbing event and no challenge event "neither writes what the
/// transcript reads nor reads what it writes", so it commutes, and central
/// transformers form a symmetric monoidal sub-category of the premonoidal
/// one. Interchange fails for everything else, which is why soundness.md
/// §9.3 must be conservative about interleaved groups.
struct TransformerExtent {
  std::string instance;
  uint64_t begin = 0;
  uint64_t end = 0;
  bool central = true;
};

/// Kernel §4's decomposition decision, computed rather than assumed: an
/// interleaved group decomposes per-transformer exactly when all but one of
/// its members is central. Groups are the transitive closure of extent
/// overlap, not merely overlapping pairs -- two non-central transformers
/// joined through a central one are one group and must be counted together.
///
/// The admitting direction is unreachable today and is implemented anyway:
/// `vocabularies.md` requires a reduction contract to declare at least one
/// round, because "a contract with no interaction rounds states no local
/// transition to judge or price", so every admitted transformer samples a
/// challenge and none is central. Writing the kernel's criterion rather than
/// the constant it currently evaluates to is what keeps this correct if that
/// vocabulary rule ever admits a bookkeeping transformer; the constant is a
/// fact about today's vocabulary, the criterion is a fact about the category.
llvm::Error
requireDecomposableTransformerGroups(std::vector<TransformerExtent> extents);

/// Whether a derivation covers the artifact rather than one site of it.
///
/// Every judgment beside this one is about a step: this reduction is
/// sound under that rule, at this cost. None of them says the thing a
/// consumer actually wants, which is that the artifact as a whole is
/// discharged — and `docs/spec/soundness.md` §8.1 already claims a
/// third party re-checks *the derivation*, a claim about a final
/// sequent the system did not produce.
///
/// The three conditions are not new checks. The seal battery decided
/// the policy and refused an escaping claim; the claim graph is already
/// in the sealed view. What is new is stating that they hold together
/// with a derivation's own coverage, which is why this lives here
/// rather than in the signature: it is an accounting statement over an
/// artifact, not a security theorem about a subject, and putting it in
/// the rule language would have needed four widenings to say something
/// the rule language is not for.
struct ArtifactJudgment {
  /// True when every condition below holds.
  bool discharged = false;
  /// The policy the artifact was sealed under. A policy other than
  /// `closed_proof` is not a defect — it is an artifact that does not
  /// claim to be closed — so the judgment reports it rather than
  /// refusing.
  std::string policy;
  /// Claims no reduction consumes and the derivation does not target.
  /// Under `closed_proof` seal admits at most the terminal claim here,
  /// so a second entry means the derivation covers one conclusion of an
  /// artifact that has several.
  std::vector<uint64_t> uncoveredClaims;
};

/// Judge whether `targetClaim` — the claim a derivation concluded about
/// — discharges the whole artifact.
ArtifactJudgment judgeArtifact(const SealedSoundnessView &sealed,
                               const ClaimRef &targetClaim);

/// Resolve the reduction output named by `site`, including the redundant
/// owner-claim equality check.
llvm::Expected<ClaimRef>
resolveReductionOutput(const SealedSoundnessView &sealed,
                       const ReductionOccurrence &site);

/// Construct the unique protocol-claim subject of an exact application site.
/// Path binding authorization is deliberately outside this function.
llvm::Expected<ProtocolClaimSubject>
subjectOf(const SealedSoundnessView &sealed, const ApplicationSite &site);

/// Resolve one consumed reduction input as a protocol-claim subject.
llvm::Expected<ProtocolClaimSubject>
resolveReductionInput(const SealedSoundnessView &sealed,
                      const ReductionOccurrence &site, uint64_t inputIndex);

/// Resolve every consumed reduction input in authenticated operand order.
llvm::Expected<ConsumedClaimVectorSubject>
resolveAllReductionInputs(const SealedSoundnessView &sealed,
                          const ReductionOccurrence &site);

/// Resolve an explicit nonempty, duplicate-free list of input positions,
/// preserving the requested order.  Equal descriptors at distinct positions
/// remain distinct because each ClaimRef carries its canonical claim index.
llvm::Expected<ConsumedClaimVectorSubject>
resolveReductionInputs(const SealedSoundnessView &sealed,
                       const ReductionOccurrence &site,
                       const std::vector<uint64_t> &inputIndices);

} // namespace zkc::soundness

#endif // ZKC_SOUNDNESS_SEALEDSOUNDNESSVIEW_H
