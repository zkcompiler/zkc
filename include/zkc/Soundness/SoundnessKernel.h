//===- SoundnessKernel.h - Owned theorem/soundness core --------*- C++ -*-===//
//
// Declaration-side core for docs/spec/soundness.md.  These values are owned
// semantic objects: no registry pointer, JSON node, MLIR handle, callback, or
// certificate representation is retained here.
//
//===----------------------------------------------------------------------===//
#ifndef ZKC_SOUNDNESS_SOUNDNESSKERNEL_H
#define ZKC_SOUNDNESS_SOUNDNESSKERNEL_H

#include "zkc/Registry/Rational.h"

#include <cstdint>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <variant>
#include <vector>

namespace zkc::soundness {

struct ExactRef {
  std::string id;
  std::string sourceRevision;
};

bool operator==(const ExactRef &lhs, const ExactRef &rhs);
bool operator!=(const ExactRef &lhs, const ExactRef &rhs);

enum class ValueSort {
  Integer,
  Rational,
  String,
  Boolean,
  Subject,
  ReductionContract,
  PathTransition,
  RoundAdjacency,
  AlgebraInstance,
  SrsInstance,
  FriDomainInstance,
};

struct TypedDeclaration {
  std::string name;
  ValueSort sort = ValueSort::String;
};

/// An exact algebraic carrier named by a theorem declaration.  This is a
/// semantic value, not a registry digest or an artifact identity.
struct AlgebraInstanceValue {
  std::string group;
  std::string fieldClass;
  registry::Rational fieldOrder;
};

bool operator==(const AlgebraInstanceValue &lhs,
                const AlgebraInstanceValue &rhs);

enum class SecurityTrack { Soundness, Knowledge, Completeness };

enum class SecurityNotion {
  SpecialSoundness,
  ComputationalSpecialSoundness,
  RoundByRound,
  StateRestoration,
  FiatShamir,
  Completeness,
};

/// Under which quantification a security statement holds: whether the
/// adversary fixes the instance before seeing the parameters, may
/// choose it after, or may additionally choose which index of a family
/// it attacks. Three different theorems about one protocol, which is
/// why this belongs to the index rather than to the subject.
enum class SecurityQuantification {
  Static,
  AdaptiveInstance,
  AdaptiveIndex,
};

struct SecurityIndex {
  SecurityNotion notion = SecurityNotion::SpecialSoundness;
  SecurityTrack track = SecurityTrack::Soundness;
  std::string variant;
  std::string model;
  SecurityQuantification quantification = SecurityQuantification::Static;
};

bool operator==(const SecurityIndex &lhs, const SecurityIndex &rhs);
bool operator!=(const SecurityIndex &lhs, const SecurityIndex &rhs);

/// A rule's description of one index, which is the index itself except
/// that `quantification` may be a variable instead of a value.
///
/// A rule with a premise either establishes the quantification or
/// carries it, and carrying it is not sayable when both sides are
/// written out in full: ten of the twenty-seven rules have premises, so
/// preservation without a variable means one rule per value. A premise
/// naming the variable matches any quantification and binds it; a
/// conclusion naming it restates whatever the premises bound, so a
/// conclusion's variable with no premise binding it is refused as
/// ill-formed. The variable is deliberately confined to this one
/// coordinate — binding `notion` or `track` would let a rule conclude
/// in a track its premise never established, which writing indices out
/// in full is what currently prevents.
struct SecurityIndexPattern {
  SecurityIndex index;
  /// When set, `index.quantification` is ignored: a premise matches
  /// any quantification and binds it under this name, and the rule's
  /// conclusion restates the name to carry it.
  std::string quantificationVariable;
};

/// Whether `index` satisfies `pattern`, binding the pattern's variable
/// into `binding` when it has one. The binding is shared across a
/// rule's premises: a second premise naming the same variable must
/// agree with the first, so the caller passes one binding for the whole
/// rule rather than one per premise.
///
/// The one shared slot is not keyed by variable name, which is correct
/// because a rule can name at most one variable: well-formedness
/// refuses a premise whose variable is not the one its conclusion
/// restates, so two distinct variables never reach this binding.
bool matchSecurityIndex(const SecurityIndexPattern &pattern,
                        const SecurityIndex &index,
                        std::optional<SecurityQuantification> &binding);

/// The index `pattern` denotes once its variable, if it has one, is
/// given the value `binding`. A pattern without a variable ignores
/// `binding` and denotes its index as written.
SecurityIndex instantiateSecurityIndex(const SecurityIndexPattern &pattern,
                                       SecurityQuantification binding);

enum class ResultSchema {
  Extraction,
  Round,
  Scalar,
};

enum class SubjectSchemaKind {
  ProtocolClaim,
  ConsumedClaimVector,
  ExternalInstance,
};

struct SubjectSchema {
  std::string ref;
  std::vector<ValueSort> argumentTypes;
  SubjectSchemaKind kind = SubjectSchemaKind::ProtocolClaim;
};

enum class ContractRoundSelectorKind {
  AllContractRounds,
  RoundKind,
  RoundPosition,
};

struct ContractRoundSelector {
  ContractRoundSelectorKind kind = ContractRoundSelectorKind::AllContractRounds;
  std::string roundKind;
  uint64_t position = 0;
};

enum class ArtifactProjectionKind {
  ConclusionReductionContract,
  ContractRoundAdjacency,
  ReductionInputCount,
  ReductionParameter,
  ContractRoundFamilyField,
  PathBindingField,
  /// The number of seal-stage bindings whose bound value is the
  /// transcript projection of a claim's declared contract anchor
  /// (docs/spec/relations.md §2.8). The projection binds 216 of the
  /// anchor's 256 bits, so the shortfall is priced as a named
  /// primitive-game advantage scaled by this count: zero where no
  /// relation identity enters the transcript, and the addend vanishes.
  BoundRelationAnchorCount,
  /// How much content stands behind the commitments a reduction's own
  /// messages carry: the arity its value profiles declare, which must be
  /// one value across them.
  ///
  /// A rule that reads this owes a condition tying it back to sealed
  /// structure. The commitment root occupies one slot whatever it commits
  /// to, so a declared arity has no structural counterpart on its own, and
  /// an understated one would understate a bound that grows in it —
  /// `kernel.md` §9.1's "verified by use" forbids exactly that. Being in
  /// the type is what makes it sealed; the rule's own condition is what
  /// makes it checked.
  CommittedArity,
};

enum class ProjectionAggregate { UniqueEqual, Count };

struct ArtifactProjection {
  ArtifactProjectionKind kind =
      ArtifactProjectionKind::ConclusionReductionContract;
  ValueSort resultSort = ValueSort::String;
  std::string field;
  uint64_t inputIndex = 0;
  ContractRoundSelector roundSelector;
  ProjectionAggregate aggregate = ProjectionAggregate::UniqueEqual;
  /// Which message role a committed-arity projection reads. Empty reads the
  /// whole reduction, which is what a rule wants when one number answers for
  /// every commitment it prices.
  std::string memberRole;
};

enum class BindingValueKind {
  Literal,
  SealedArtifactProjection,
  ConclusionSubject,
  ApplicationPathTransition,
  ConclusionResource,
  ResolvedParameter,
};

struct BindingValue {
  BindingValueKind kind = BindingValueKind::Literal;
  ValueSort sort = ValueSort::String;
  std::variant<registry::Rational, std::string, bool, AlgebraInstanceValue>
      literal = std::string();
  std::string reference;
  std::string premisePort;
  ArtifactProjection artifactProjection;
};

bool operator==(const ContractRoundSelector &lhs,
                const ContractRoundSelector &rhs);
bool operator==(const ArtifactProjection &lhs, const ArtifactProjection &rhs);

/// Structural equality of two value sources.  Two equal sources read the same
/// thing, so a condition argument equal to a parameter's own binding is that
/// parameter rather than a second value that happens to agree today.
bool operator==(const BindingValue &lhs, const BindingValue &rhs);

enum class QuantityKind {
  RationalLiteral,
  Parameter,
  ArtifactFact,
  ContractRoundFact,
  PremiseCoordinate,
  ResourceVariable,
  Add,
  Sub,
  Mul,
  Div,
  Pow,
  Pow2,
  Pow2Up,
};

enum class ContractRoundField {
  ChallengeSpace,
  ChallengeCount,
  RoundDegree,
  ChallengeSpaceLog2,
};

enum class PremiseCoordinateField {
  Arity,
  ChallengeSpace,
};

/// The only way to name a premise coordinate.
///
/// `SpecialSoundnessToRoundByRound` binds one coordinate index inside its
/// per-coordinate bound, and section 5.1 of docs/spec/soundness.md admits no
/// second selector: a free string naming a coordinate would be an iterator
/// over the premise, not a projection of it.
enum class PremiseCoordinateSelectorKind {
  BoundCoordinate,
};

struct PremiseCoordinateSelector {
  PremiseCoordinateSelectorKind kind =
      PremiseCoordinateSelectorKind::BoundCoordinate;
};

struct QuantityTemplate {
  QuantityKind kind = QuantityKind::RationalLiteral;
  registry::Rational literal;
  std::string name;
  std::string port;
  std::string caseName;
  ContractRoundField contractRoundField = ContractRoundField::ChallengeSpace;
  PremiseCoordinateField premiseCoordinateField = PremiseCoordinateField::Arity;
  PremiseCoordinateSelector premiseCoordinateSelector;
  std::vector<QuantityTemplate> operands;

  static QuantityTemplate rational(registry::Rational value);
  static QuantityTemplate named(QuantityKind kind, std::string name);
  static QuantityTemplate node(QuantityKind kind,
                               std::vector<QuantityTemplate> operands);
};

struct PrimitiveGameDefinition {
  ExactRef ref;
  std::vector<ValueSort> instanceArgumentTypes;
  std::vector<TypedDeclaration> resources;
};

struct PrimitiveGameInstanceTemplate {
  std::string gameRef;
  std::vector<BindingValue> instanceArguments;
};

/// The constructors a rule body can form.
///
/// A projection of a premise result is admitted only for the schemas a body
/// can actually place in a bound: the only bodies with a free bound slot take
/// no premise, a special-soundness premise, a round-by-round premise, or a
/// state-restoration premise, so `ScalarBound` is the one projection
/// reachable — a round-by-round premise reaches none of them, because there is
/// no round projection constructor.  Constructors for premise
/// schemas no body admits are not kept against a future composition body:
/// evaluator code that must be trusted but cannot be invoked is not free, and
/// a constructor is reintroduced only alongside a body that reaches it, so its
/// semantics and tests can be reviewed against a concrete use.
enum class RuleBoundKind {
  Quantity,
  ScalarBound,
  PrimitiveAdvantage,
  Add,
  Scale,
  Max,
};

struct RuleBound {
  RuleBoundKind kind = RuleBoundKind::Quantity;
  QuantityTemplate quantity;
  std::string premisePort;
  PrimitiveGameInstanceTemplate game;
  std::map<std::string, QuantityTemplate, std::less<>> gameResourceSubstitution;
  std::vector<RuleBound> operands;
};

struct CoordinateTemplate {
  std::string label;
  QuantityTemplate arity;
  std::optional<QuantityTemplate> challengeSpace;
};

enum class ContractLabelProjection {
  RoundIndex,
  RoundKindOccurrence,
  CaseName,
  /// A contract-local index repeats at every occurrence of that contract, so a
  /// row that composes two occurrences of one contract cannot tell their
  /// rounds apart.  This qualifies the index by the occurrence's canonical
  /// transformer position, which is the occurrence's own identity.  Opt-in per
  /// case, so a row that does not compose keeps contract-local labels and its
  /// witness is unchanged (docs/spec/soundness.md §5.1).
  SiteQualifiedRoundIndex,
};

struct ContractCoordinateCase {
  std::string caseName;
  ContractRoundSelector selector;
  ContractLabelProjection labelProjection = ContractLabelProjection::RoundIndex;
  QuantityTemplate arity;
  std::optional<QuantityTemplate> challengeSpace;
};

struct CoordinateSequence {
  enum class Kind { Explicit, Contract } kind = Kind::Explicit;
  std::vector<CoordinateTemplate> coordinates;
  std::string contractFactPort;
  std::vector<ContractCoordinateCase> cases;
};

struct RoundTemplate {
  std::string roundIndex;
  QuantityTemplate challengeSpace;
  RuleBound bound;
};

struct ContractRoundCase {
  std::string caseName;
  ContractRoundSelector selector;
  ContractLabelProjection indexProjection = ContractLabelProjection::RoundIndex;
  QuantityTemplate challengeSpace;
  RuleBound bound;
};

struct RoundSequence {
  enum class Kind { Explicit, Contract } kind = Kind::Explicit;
  std::vector<RoundTemplate> rounds;
  std::string contractFactPort;
  std::vector<ContractRoundCase> cases;
};

enum class RoundSelectorKind {
  ByRoundIndex,
  AdjacentPredecessorRound,
};

struct RoundSelectorTemplate {
  RoundSelectorKind kind = RoundSelectorKind::ByRoundIndex;
  std::string exactRoundIndex;
  std::string adjacencyFactPort;
};

enum class PremiseResultConstraint {
  RequiresEmptyGameSupport,
  RequiresNoBoundResourceSupport,
};

struct PremisePort {
  std::string name;
  std::string expectedSubjectSchema;
  SecurityIndexPattern expectedIndex;
  ResultSchema expectedResult = ResultSchema::Extraction;
  std::vector<TypedDeclaration> expectedResources;
  std::set<PremiseResultConstraint> resultConstraints;
  std::map<std::string, QuantityTemplate, std::less<>> resourceSubstitution;
};

struct MachineConditionTemplate {
  std::string slot;
  std::string predicateRef;
  std::vector<ValueSort> argumentTypes;
};

struct ExternalHypothesisTemplate {
  std::string slot;
  std::string propositionRef;
  std::vector<ValueSort> argumentTypes;
};

/// Pin one declared rule parameter to an exact literal at APPLY time. This is
/// the only closed equality form needed by the v0 inventory; it deliberately
/// does not expose a general binding-to-binding equality language.
struct ExactParameterPin {
  std::string parameter;
  BindingValue expected;
};

struct SpecialSoundnessEntry {
  CoordinateSequence coordinates;
};

struct NativeRoundByRoundEntry {
  RoundSequence rounds;
};

struct ComputationalEntry {
  CoordinateSequence coordinates;
  RuleBound failureBound;
};

/// The honest-prover acceptance-failure bound, stated directly by the cited
/// theorem (0 for perfect completeness).  A completeness judgment says
/// nothing about any adversary, which is why its conclusion index carries the
/// completeness notion and track rather than borrowing a soundness spelling
/// (docs/spec/soundness.md §3.2).
struct CompletenessEntry {
  RuleBound bound;
};

struct SpecialSoundnessPreservation {
  std::string sourcePort;
  CoordinateSequence appendedCoordinates;
  RuleBound conclusionFailureBound;
};

/// Compose a round-by-round premise with this reduction's own rounds by
/// concatenating their round sequences.  The composed error is a reindexing of
/// the components' error functions, not their sum and not their maximum, so
/// nothing here combines two bounds numerically: every round keeps the bound
/// its own component gave it.  Two fields, where the special-soundness
/// preservation beside it has three, because a round result carries no
/// conclusion-level failure bound to close (docs/spec/soundness.md §5.1).
struct RoundByRoundPreservation {
  std::string sourcePort;
  RoundSequence appendedRounds;
};

struct RoundScaling {
  std::string roundByRoundPort;
  RoundSelectorTemplate selectedRound;
  QuantityTemplate scale;
};

struct SpecialSoundnessToRoundByRound {
  std::string specialSoundnessPort;
  RuleBound perCoordinateBound;
};

struct RoundByRoundToStateRestoration {
  std::string roundByRoundPort;
  QuantityTemplate moveBudget;
};

struct StateRestorationToFiatShamirDuplex {
  std::string stateRestorationPort;
  RuleBound localDuplexBound;
};

using RuleBody =
    std::variant<SpecialSoundnessEntry, NativeRoundByRoundEntry,
                 ComputationalEntry, CompletenessEntry,
                 SpecialSoundnessPreservation, RoundByRoundPreservation,
                 RoundScaling, SpecialSoundnessToRoundByRound,
                 RoundByRoundToStateRestoration,
                 StateRestorationToFiatShamirDuplex>;

/// Whether this signature offers the rule for execution.
///
/// A declared rule is well-formed and inspectable but unreachable: no binding
/// may name it, so no derivation can apply it.  This is a signature-authoring
/// decision recorded as declaration content, not a judgment about whether the
/// cited theorem is true; the kernel forms no such judgment (docs/spec/
/// soundness.md §5.1).  Reasons an author would choose it — a refuted source, a
/// rule that only states what a provider supplies, a superseded revision — are
/// annotations, which live outside the declaration entirely.
enum class RuleStatus {
  Admitted,
  Declared,
};

struct SoundnessRule {
  ExactRef ref;
  RuleStatus status = RuleStatus::Admitted;
  std::vector<TypedDeclaration> parameters;
  std::vector<TypedDeclaration> resources;
  std::vector<PremisePort> premises;
  std::vector<TypedDeclaration> artifactFacts;
  std::vector<MachineConditionTemplate> machineConditions;
  std::vector<ExternalHypothesisTemplate> externalHypotheses;
  std::vector<ExactParameterPin> exactParameterPins;
  SecurityIndexPattern conclusionIndex;
  RuleBody body;
};

enum class ConsumedClaimSelectorKind {
  ReductionInput,
  AllReductionInputs,
  ReductionInputs,
};

enum class SubjectRelationKind {
  SameSubject,
  ConsumedClaim,
  ConsumedClaimVector,
  ExactExternalSubject,
};

struct SubjectRelation {
  SubjectRelationKind kind = SubjectRelationKind::SameSubject;
  ConsumedClaimSelectorKind selector =
      ConsumedClaimSelectorKind::ReductionInput;
  std::vector<uint64_t> inputIndices;
  std::string externalSubjectSchema;
  std::vector<BindingValue> externalArguments;
};

enum class ProtocolAnchorKind { ReductionContract, PathTransition };

struct ProtocolAnchor {
  ProtocolAnchorKind kind = ProtocolAnchorKind::ReductionContract;
  ExactRef ref;
};

struct RuleBinding {
  ExactRef ref;
  ExactRef ruleRef;
  std::string subjectSchema;
  ProtocolAnchor anchor;
  std::map<std::string, SubjectRelation, std::less<>> premiseRelations;
  std::map<std::string, BindingValue, std::less<>> parameterBindings;
  std::map<std::string, BindingValue, std::less<>> factBindings;
  std::map<std::string, std::vector<BindingValue>, std::less<>>
      conditionArgumentBindings;
  std::map<std::string, std::vector<BindingValue>, std::less<>>
      hypothesisArgumentBindings;
};

enum class MachineDeciderKind {
  OneMessageRole,
  SpaceEmbeds,
  BoundBites,
  FieldClass,
  SpaceCoversArity,
  BatchArity,
  SpaceCoversBatch,
  SamePoint,
  BatchAfterMaterial,
  FriShape,
  JohnsonFoldParam,
  JohnsonSlack,
  JohnsonMultiplicity,
  JohnsonDelta,
  UdrDomainFloor,
  UdrThetaWindow,
  RandomWordsEtaFloor,
  ThresholdDeltaWindow,
  PowPinned,
  PowAdjacent,
  DuplexSpine,
  CodecBiasDeclared,
  /// The multiplicity sequence is indexed by the table, so its committed
  /// arity equals the table's.
  ///
  /// This is the one arity relation the artifact fixes, and the reason it is
  /// checkable: Lemma 5's witness has one field element per table entry, so a
  /// multiplicity column of another length is not the object the theorem
  /// quantifies over. It is not a tie between a declaration and what was
  /// committed — no such tie exists in a transcript, and that gap is carried
  /// as an external hypothesis instead (see the value-profile discussion in
  /// docs/spec/carrier.md §3).
  MultiplicitiesMatchTable,
  /// Every anchor of every consumed claim names transcript material that
  /// entered before the round's challenge.
  ///
  /// A reduction's bound prices a passage from what its consumed claim says
  /// to what its produced claim says. If the consumed claim is anchored to
  /// material the round never saw, the two statements are about different
  /// objects and no theorem relates them — the transition's probability is
  /// one, whatever the bound says. Produced anchors are constructor-derived
  /// and checked against the spine already; this is the same discipline on
  /// the side the artifact declares.
  ConsumedAnchorsAreRoundMaterial,
  /// The lemma's own hypothesis: multiplicities are field elements, so the
  /// number of entries must stay below the characteristic. Overflowing
  /// multiplicities are the known soundness failure of the whole approach
  /// (Haböck, ePrint 2022/1530, Lemma 5), so a rule without this prices a
  /// protocol the theorem does not cover.
  LookupFitsCharacteristic,
};

struct MachineDeciderDefinition {
  ExactRef ref;
  std::vector<ValueSort> argumentTypes;
  MachineDeciderKind kind = MachineDeciderKind::OneMessageRole;
};

struct PropositionSchema {
  ExactRef ref;
  std::vector<ValueSort> argumentTypes;
};

struct SchemaContext {
  std::vector<SecurityIndex> securityIndices;
  std::map<std::string, SubjectSchema, std::less<>> subjectSchemas;
  std::map<std::string, PrimitiveGameDefinition, std::less<>> primitiveGames;
  std::map<std::string, MachineDeciderDefinition, std::less<>> machineDeciders;
  std::map<std::string, PropositionSchema, std::less<>> propositions;
};

enum class RuleWfRefusalCode {
  InvalidReference,
  DuplicateDeclaration,
  UnknownSchema,
  InvalidIndex,
  InvalidBodySignature,
  InvalidQuantity,
  InvalidBound,
  InvalidSequence,
  InvalidPrimitiveGame,
  InvalidCondition,
  InvalidHypothesis,
  InvalidResourceSubstitution,
  MissingRbrToSrConstraint,
  InvalidBinding,
  InvalidSubjectRelation,
  RuleNotBindable,
};

struct RuleWfRefusal {
  RuleWfRefusalCode code = RuleWfRefusalCode::InvalidReference;
  std::string location;
  std::string detail;
};

struct RuleWfResult {
  std::optional<RuleWfRefusal> refusal;

  bool accepted() const { return !refusal.has_value(); }
};

RuleWfResult checkRuleWellFormed(const SchemaContext &context,
                                 const SoundnessRule &rule);

/// Check a complete binding against one well-formed rule.  This judgment owns
/// exact slot coverage, subject-relation shape, and typed value-source shape.
/// Artifact/site-dependent resolution remains an APPLY-time judgment.
RuleWfResult checkRuleBindingWellFormed(const SchemaContext &context,
                                        const SoundnessRule &rule,
                                        const RuleBinding &binding);


const char *ruleWfRefusalCodeName(RuleWfRefusalCode code);
const char *ruleStatusName(RuleStatus status);

} // namespace zkc::soundness

#endif // ZKC_SOUNDNESS_SOUNDNESSKERNEL_H
