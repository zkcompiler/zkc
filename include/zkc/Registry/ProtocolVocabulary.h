//===- ProtocolVocabulary.h - Protocol vocabulary -------------*- C++ -*-===//
#ifndef ZKC_REGISTRY_PROTOCOLVOCABULARY_H
#define ZKC_REGISTRY_PROTOCOLVOCABULARY_H

#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"
#include <cstdint>
#include <map>
#include <optional>
#include <string>
#include <vector>

namespace zkc {
namespace registry {

/// The exact descriptor shape carried by one claim profile. Anchors are a
/// duplicate-free name set, stored in lexical order.
struct ClaimProfile {
  std::string kind;
  std::vector<std::string> anchors;
  std::string digest;

  llvm::StringRef contentDigest() const { return digest; }
  llvm::json::Value toCanonicalJson() const;
};

/// What a value commits to, for a value whose type names a profile rather
/// than a bare payload class: the schema is docs/spec/carrier.md §7, and
/// what a profiled value is — a commitment rather than an element of the
/// class its content is drawn from — is §3.
///
/// The claim type has resolved a descriptor profile since the beginning; the
/// value type carried one string, and every mechanism that needed to state
/// what a commitment binds had to reconstruct it on the rule side. This is
/// that type given the treatment the other one already had, and the anchor
/// precedent carries over exactly: the profile fixes the arity, the element
/// class and the binding route, and the kernel never reads the committed
/// data. No-predicate-semantics is preserved by construction.
///
/// `arityLog2` is the base-two logarithm of how many elements stand behind
/// the commitment. It is a rule-readable fact rather than a producer
/// annotation, which is the point: the logup error `(n+m)/|F|` increases in
/// the table arity, so a declared arity could understate a bound, and
/// `kernel.md` §9.1 forbids exactly that. A rule that reads it owes a
/// condition tying it back to sealed structure.
struct ValueProfile {
  /// The payload class of one element, which is what keys `kappa.codecs`.
  std::string elementClass;
  /// Where the committed content comes from. `prover_message` is material
  /// the prover chose; `relation_derived` is derived from the relation the
  /// artifact is about; `preprocessed` is fixed before any statement.
  ///
  /// Only `prover_message` has a carrier that can express it: a profile
  /// belongs to a slot, and a slot is prover material. The other two are
  /// admitted so the relation commitment and the preprocessed index arrive
  /// as values of this field rather than as sibling mechanisms; until a
  /// statement-side value can carry a profile, declaring one of them says
  /// something the artifact cannot mean.
  std::string origin;
  int64_t arityLog2 = 0;
  /// The construction that realizes the commitment. Carried into the
  /// profile's content digest, so two artifacts naming different routes are
  /// different protocols -- and checked against nothing else: no registry
  /// resolves a route name today, so this records what the author declared
  /// rather than authenticating it.
  std::string bindingRoute;
  std::string digest;

  llvm::StringRef contentDigest() const { return digest; }
  llvm::json::Value toCanonicalJson() const;
};

enum class CheckMode { Opaque, Transparent };

enum class CheckPredicateFormat {
  TransparentExpressionV1,
  OpaquePredicateSpecV1,
};

/// Digest-covered commitment to the mathematical acceptance predicate behind
/// a CheckContract.  Transparent checks bind the normalized in-artifact
/// expression language; opaque checks pin one separately shipped canonical
/// predicate-spec object by exact content digest and entrypoint.
struct CheckPredicateDescriptor {
  CheckPredicateFormat format = CheckPredicateFormat::TransparentExpressionV1;
  std::string contentDigest;
  std::string entrypoint;

  llvm::json::Value toCanonicalJson() const;
};

enum class OperandMultiplicityKind { Exact, Capture, SameAs };

/// A positional operand segment. `value` is the exact count for Exact and the
/// lower bound for Capture; `name` is the capture name for Capture/SameAs.
struct OperandMultiplicity {
  OperandMultiplicityKind kind = OperandMultiplicityKind::Exact;
  uint64_t value = 1;
  std::string name;

  llvm::json::Value toCanonicalJson() const;
};

struct CheckOperandSegment {
  std::string role;
  std::string valueClass;
  OperandMultiplicity multiplicity;

  llvm::json::Value toCanonicalJson() const;
};

/// Closed ABI and normative acceptance text for one opaque predicate
/// entrypoint.  The ABI deliberately reuses CheckContract's operand algebra:
/// a loader can compare the two structures directly, without interpreting a
/// second signature language.  `acceptance` specifies the mathematical
/// predicate and its unsupported cases; executing it remains a separate
/// assurance facet.
struct CheckPredicateEntrypoint {
  std::vector<std::string> acceptance;
  std::vector<std::string> parameters;
  std::vector<std::string> semanticParameters;
  std::vector<CheckOperandSegment> operands;

  llvm::json::Value toCanonicalJson() const;
};

/// One content-addressed opaque predicate specification.  Its map key is the
/// exact digest of `toCanonicalJson()` under
/// `zkc/check-predicate-spec\n`; aliases and mutable names are absent.
struct CheckPredicateSpec {
  std::string title;
  std::optional<std::vector<std::string>> references;
  std::map<std::string, CheckPredicateEntrypoint, std::less<>> entrypoints;
  std::string digest;

  llvm::StringRef contentDigest() const { return digest; }
  llvm::json::Value toCanonicalJson() const;
};

/// One verifier-check contract. The vocabulary entry id is a human-readable
/// lookup and diagnostic handle; the exact content digest binds the predicate
/// descriptor and structural ABI and is the projection/dispatch authority.
/// Executable adapter conformance is a separate assurance facet. There is
/// deliberately no second carrier-kind namespace.
struct CheckContract {
  CheckMode mode = CheckMode::Opaque;
  CheckPredicateDescriptor predicate;
  /// Duplicate-free name sets, stored in lexical order to match keyed carrier
  /// dictionaries. Only operand segments are positional.
  std::vector<std::string> parameters;
  std::vector<std::string> semanticParameters;
  std::vector<CheckOperandSegment> operands;
  std::string digest;

  bool isTransparent() const { return mode == CheckMode::Transparent; }
  llvm::StringRef contentDigest() const { return digest; }
  llvm::json::Value toCanonicalJson() const;
};

/// The carrier sort of one hole-contract segment: a runtime value (with
/// payload class and count), an opaque threaded handle (with handle
/// class), or — pow_search operand/result only — the transcript
/// snapshot itself.
enum class HoleSegmentSort { Value, Handle, Sponge };

/// One typed operand or result segment of a prover compute hole
/// (docs/spec/vocabularies.md §5.1). Roles are readable dataflow
/// names for route references; positions are the ABI.
struct HoleSegment {
  std::string role;
  HoleSegmentSort sort = HoleSegmentSort::Value;
  /// Payload class (value segments) or handle class (handle segments);
  /// empty exactly for the sponge sort.
  std::string typeClass;
  /// "1" for a scalar value, a canonical decimal for a vector value;
  /// empty for handle and sponge segments.
  std::string count;
  llvm::json::Value toCanonicalJson() const;
};

/// One prover compute-hole contract. `kind` classifies the primary
/// output for diagnostics and coverage bucketing; the typed signature
/// is the authority, and the content digest is the sole dispatch
/// authority, exactly as check contracts fix it. A hole has no protocol
/// effects; only a pow_search hole declares sponge segments (one
/// operand, one result, state-identical by semantic requirement).
struct HoleContract {
  std::string kind;
  std::vector<HoleSegment> operands;
  std::vector<HoleSegment> results;
  /// Duplicate-free name sets in lexical order, mirroring check
  /// contracts: `parameters` are static instance values;
  /// `semanticParameters` are digest-shaped identities (an SRS, a
  /// verifier key) the supplier must hold matching content for.
  std::vector<std::string> parameters;
  std::vector<std::string> semanticParameters;
  std::string digest;

  llvm::StringRef contentDigest() const { return digest; }
  llvm::json::Value toCanonicalJson() const;
};

enum class MessageMultiplicityKind { Exact, ConsumedClaims };

/// The number of transcript messages carried by one role. Dynamic
/// multiplicity is deliberately limited to the reduction's consumed-claim
/// arity: this is the one instance-local cardinality already admitted by a
/// variadic consume pattern, rather than a second unconstrained count source.
struct MessageMultiplicity {
  MessageMultiplicityKind kind = MessageMultiplicityKind::Exact;
  uint64_t exact = 0;

  bool isDynamic() const {
    return kind == MessageMultiplicityKind::ConsumedClaims;
  }
  uint64_t resolve(uint64_t consumedClaims) const {
    return isDynamic() ? consumedClaims : exact;
  }
  llvm::json::Value toCanonicalJson() const;
};

struct VocabularyMessageRole {
  std::string role;
  MessageMultiplicity multiplicity;
};

/// One priced use of a transcript-derived challenge capability.  The role
/// names a dependency slot; `count == 0` is the canonical scalar form (the
/// JSON field is absent), while `count >= 2` requires the capability's vector
/// mode to have exactly that many samples.  Explicit `count: 1` is rejected so
/// one realized use cannot have two content spellings.  This is deliberately
/// a round fact, not a producer/source fact:
/// a challenge capability may be carried as an ordinary dependency without
/// thereby becoming a theorem-priced round.
struct VocabularyChallengeUse {
  std::string role;
  uint64_t count = 0;

  llvm::json::Value toCanonicalJson() const;
};

struct VocabularyRound {
  VocabularyChallengeUse challengeUse;
  std::vector<VocabularyMessageRole> messages;
  std::string kind;
};

/// Closed provenance constraint for a reduction dependency.  `Any` constrains
/// only the payload class; the other cases require the value to be produced by
/// the named carrier capability.  This axis is orthogonal to challenge use:
/// rounds, not this enum, identify the dependencies whose sample spaces enter
/// theorem pricing.
enum class VocabularyDepSource {
  Any,
  PublicBind,
  ProverSlot,
  ChallengeCapability,
};

struct VocabularyDepSlot {
  std::string role;
  VocabularyDepSource source = VocabularyDepSource::Any;
  std::string payloadClass;
};

/// A plain consume pattern has min == 0 and consumes exactly one claim. A
/// variadic pattern has min >= 1 and must be the contract's only consume entry.
struct VocabularyConsumePattern {
  std::string profile;
  uint64_t min = 0;

  bool isVariadic() const { return min != 0; }
};

enum class ReductionParameterSort { Atom, MaterialRef, MaterialRefVector };

enum class MaterialExprSort { Ref, Refs, Claim, Claims, Atom };

enum class MaterialOrder { Operand, CanonicalUnique };

enum class MaterialExprKind {
  LiteralRef,
  InputAnchor,
  Dependency,
  Message,
  ParameterRef,
  Construct,
  InputAnchors,
  Messages,
  ParameterRefs,
  List,
  InputDescriptor,
  InputDescriptors,
  ParameterAtom,
  Literal,
};

/// One node in the closed, many-sorted symbolic material algebra. The generic
/// fields are interpreted only by `kind`: `name` carries a role, anchor,
/// parameter, tag, or literal reference; `index` carries an input or message
/// occurrence; `arguments` carries construct/list children; and `literal`
/// carries the canonical kernel-domain value of a Literal node.
struct MaterialExpr {
  MaterialExprKind kind = MaterialExprKind::LiteralRef;
  MaterialExprSort sort = MaterialExprSort::Ref;
  std::string name;
  uint64_t index = 0;
  MaterialOrder order = MaterialOrder::Operand;
  std::vector<MaterialExpr> arguments;
  llvm::json::Value literal = nullptr;

  llvm::json::Value toCanonicalJson() const;
};

enum class ReductionCheckAttachmentKind {
  SemanticParameter,
  MaterialRefEquality,
  ValueIdentity,
  MaterialRefVectorEquality,
  CommonMaterialRefEquality,
  ValueIdentityVector,
  ValueIdentityList,
};

/// One exact edge from reduction context into a selected check. The enclosing
/// body-check slot supplies the check role; `targetRole` names either one
/// semantic argument or one solved operand segment according to `kind`.
struct ReductionCheckAttachment {
  ReductionCheckAttachmentKind kind =
      ReductionCheckAttachmentKind::MaterialRefEquality;
  MaterialExpr source;
  std::string targetRole;

  llvm::json::Value toCanonicalJson() const;
};

struct BodyCheckSlot {
  std::string contract;
  std::map<std::string, llvm::json::Value, std::less<>> parameters;
  std::optional<llvm::json::Value> transparentPredicate;
  std::vector<ReductionCheckAttachment> attachments;

  llvm::json::Value toCanonicalJson() const;
};

struct MaterialConstraint {
  MaterialExpr left;
  MaterialExpr right;

  llvm::json::Value toCanonicalJson() const;
};

struct ReductionOutputConstructor {
  std::string profile;
  std::map<std::string, MaterialExpr, std::less<>> anchors;

  llvm::json::Value toCanonicalJson() const;
};

/// One authority for both reduction shape and its exact local implication.
/// Its digest transitively covers every referenced claim profile and body
/// check contract. Output constructors, rather than a parallel `produces`
/// table, are the positional produced-profile authority.
struct ReductionContract {
  std::vector<VocabularyConsumePattern> consumes;
  std::vector<VocabularyDepSlot> depSlots;
  std::vector<VocabularyRound> rounds;
  std::map<std::string, ReductionParameterSort, std::less<>> parameters;
  std::map<std::string, BodyCheckSlot, std::less<>> checks;
  std::vector<MaterialConstraint> constraints;
  std::vector<ReductionOutputConstructor> outputs;
  std::string digest;

  llvm::StringRef contentDigest() const { return digest; }
  llvm::json::Value toCanonicalJson() const;
};

enum class AttachmentSourceKind {
  ClaimAnchor,
  ProducerInputAnchor,
  ProducerInputsAnchor,
  ProducerInputDescriptors,
  ProducerDependency,
  ProducerMessage,
};

/// Flat tagged representation of the closed attachment-source algebra.
/// Fields not selected by `kind` remain empty/zero.
struct AttachmentSource {
  AttachmentSourceKind kind = AttachmentSourceKind::ClaimAnchor;
  std::string anchor;
  std::string role;
  uint64_t index = 0;

  llvm::json::Value toCanonicalJson() const;
};

enum class TerminalAttachmentKind {
  SemanticParameter,
  MaterialRefEquality,
  ValueIdentity,
  MaterialRefVectorEquality,
  CommonMaterialRefEquality,
  DescriptorDigest,
};

/// Flat tagged representation of one terminal attachment. `checkRole` is the
/// terminal-rule role and `targetRole` is a semantic-parameter or operand
/// role. `claimAnchor` is used by descriptor/common-reference variants.
struct TerminalAttachment {
  TerminalAttachmentKind kind = TerminalAttachmentKind::SemanticParameter;
  AttachmentSource source;
  std::string checkRole;
  std::string targetRole;
  std::string claimAnchor;

  llvm::json::Value toCanonicalJson() const;
};

struct TerminalProducerPin {
  std::string contract;
  uint64_t output = 0;
};

/// A terminal rule closes one exact claim profile through named check roles.
/// The digest transitively covers the referenced profile, optional producer
/// reduction contract, and all check contracts.
struct TerminalRule {
  std::string claimProfile;
  std::optional<TerminalProducerPin> producer;
  std::map<std::string, std::string, std::less<>> checks;
  std::vector<TerminalAttachment> attachments;
  std::map<std::string, llvm::json::Value, std::less<>> transparentPredicates;
  std::string digest;

  llvm::StringRef contentDigest() const { return digest; }
  llvm::json::Value toCanonicalJson() const;
};

/// One closed, cross-admitted protocol vocabulary. Admission proceeds in
/// dependency order (claim profiles, value profiles, predicate specs, check
/// contracts, hole contracts, reduction contracts, terminal rules), so an
/// unresolved reference is never retained for a later caller to interpret.
///
/// File format:
/// {
///   "registry": "zkc.protocol_vocabulary",
///   "claim_profiles": {...},
///   "value_profiles": {...},
///   "predicate_specs": {"sha256:<content digest>": {...}},
///   "check_contracts": {...},
///   "hole_contracts": {...},
///   "reduction_contracts": {...},
///   "terminal_rules": {...}
/// }
class ProtocolVocabulary {
public:
  static llvm::Expected<ProtocolVocabulary> loadFromFile(llvm::StringRef path);
  static llvm::Expected<ProtocolVocabulary> parse(llvm::StringRef json,
                                                  llvm::StringRef sourceName);

  const ClaimProfile *lookupProfile(llvm::StringRef id) const;
  const ValueProfile *lookupValueProfile(llvm::StringRef id) const;
  const CheckContract *lookupCheckContract(llvm::StringRef id) const;
  const HoleContract *lookupHoleContract(llvm::StringRef id) const;
  const ReductionContract *lookupReductionContract(llvm::StringRef id) const;
  const TerminalRule *lookupRule(llvm::StringRef id) const;

  const std::map<std::string, ClaimProfile, std::less<>> &profiles() const {
    return profiles_;
  }
  const std::map<std::string, ValueProfile, std::less<>> &
  valueProfiles() const {
    return valueProfiles_;
  }
  const std::map<std::string, CheckPredicateSpec, std::less<>> &
  predicateSpecs() const {
    return predicateSpecs_;
  }
  const std::map<std::string, CheckContract, std::less<>> &
  checkContracts() const {
    return checkContracts_;
  }
  const std::map<std::string, HoleContract, std::less<>> &
  holeContracts() const {
    return holeContracts_;
  }
  const std::map<std::string, ReductionContract, std::less<>> &
  reductionContracts() const {
    return reductionContracts_;
  }
  const std::map<std::string, TerminalRule, std::less<>> &rules() const {
    return rules_;
  }

  /// Normalized complete envelope. Artifact identity cites the required entry
  /// digests individually; opaque predicate bodies are their closed transitive
  /// preimages, not a second artifact-stamp namespace.
  llvm::json::Value toCanonicalJson() const;

private:
  std::map<std::string, ClaimProfile, std::less<>> profiles_;
  std::map<std::string, ValueProfile, std::less<>> valueProfiles_;
  std::map<std::string, CheckPredicateSpec, std::less<>> predicateSpecs_;
  std::map<std::string, CheckContract, std::less<>> checkContracts_;
  std::map<std::string, HoleContract, std::less<>> holeContracts_;
  std::map<std::string, ReductionContract, std::less<>> reductionContracts_;
  std::map<std::string, TerminalRule, std::less<>> rules_;
};

} // namespace registry
} // namespace zkc

#endif // ZKC_REGISTRY_PROTOCOLVOCABULARY_H
