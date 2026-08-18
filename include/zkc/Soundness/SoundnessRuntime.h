//===- SoundnessRuntime.h - Owned closed soundness values -------*- C++ -*-===//
//
// Runtime-side semantic values for the theorem/soundness core.  These values
// are closed and owned: they retain no MLIR handle, registry object, callback,
// certificate, or execution session.
//
//===----------------------------------------------------------------------===//
#ifndef ZKC_SOUNDNESS_SOUNDNESSRUNTIME_H
#define ZKC_SOUNDNESS_SOUNDNESSRUNTIME_H

#include "zkc/Soundness/SealedSoundnessView.h"
#include "zkc/Soundness/SoundnessKernel.h"

#include <cstdint>
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <variant>
#include <vector>

namespace zkc::soundness {

/// The semantic phase that refused a runtime object.  Later APPLY/DERIVE
/// implementations can reuse this vocabulary without introducing an
/// unstructured error channel.
enum class RuntimePhase {
  ValueValidation,
  SubjectValidation,
  QuantityValidation,
  BoundValidation,
  ResultValidation,
  HypothesisValidation,
  JudgmentValidation,
  SiteResolution,
  BindingResolution,
  PremiseResolution,
  ConditionEvaluation,
  EqualitySolving,
  ResourceSpecialization,
  RuleEvaluation,
  Derivation,
};

enum class RuntimeRefusalCode {
  InvalidReference,
  NullRecursiveValue,
  RecursiveCycle,
  SortMismatch,
  InvalidPayload,
  EmptyCollection,
  DuplicateName,
  NonCanonicalNormalForm,
  InvalidResource,
  UnknownSchema,
  UnknownIndex,
  InvalidResultSchema,
  InvalidPrimitiveGame,
  InvalidProposition,
  SiteMismatch,
  BindingMismatch,
  PremiseMismatch,
  CoverageMismatch,
  ConditionFailed,
  EqualityMismatch,
  ArithmeticDomain,
  UnsupportedNormalForm,
};

struct SoundnessRefusal {
  RuntimePhase phase = RuntimePhase::ValueValidation;
  RuntimeRefusalCode code = RuntimeRefusalCode::InvalidPayload;
  std::string location;
  std::string detail;
};

struct RuntimeCheckResult {
  std::optional<SoundnessRefusal> refusal;

  bool accepted() const { return !refusal.has_value(); }
};

const char *runtimePhaseName(RuntimePhase phase);
const char *runtimeRefusalCodeName(RuntimeRefusalCode code);

/// A closed scalar carried by an authenticated contract or path field.
/// Only the three projection-visible scalar sorts are admitted.
struct ExactScalarValue {
  ValueSort sort = ValueSort::String;
  std::variant<registry::Rational, std::string, bool> payload = std::string();
};

bool operator==(const ExactScalarValue &lhs, const ExactScalarValue &rhs);
bool operator!=(const ExactScalarValue &lhs, const ExactScalarValue &rhs);

/// One authenticated interaction round, in contract order.
struct ReductionContractRoundValue {
  registry::Rational roundIndex;
  std::string roundKind;
  std::string challengeRole;
  uint64_t challengeEventPosition = 0;
  std::string challengePayloadClass;
  std::string challengeDomain;
  registry::Rational challengeSpace;
  registry::Rational challengeCount = registry::Rational::fromInteger(1);
  ChallengeShape challengeShape = ChallengeShape::Scalar;
  ChallengeSampling challengeSampling = ChallengeSampling::Uniform;
  std::vector<SealedMessageRoleFact> messages;
  std::optional<registry::Rational> roundDegree;
  std::optional<registry::Rational> challengeSpaceLog2;
};

bool operator==(const ReductionContractRoundValue &lhs,
                const ReductionContractRoundValue &rhs);
bool operator!=(const ReductionContractRoundValue &lhs,
                const ReductionContractRoundValue &rhs);

/// Exact owned contract facts available to reduction-site projections.
struct ReductionContractValue {
  ExactRef ref;
  uint64_t inputCount = 0;
  std::vector<std::map<std::string, std::string, std::less<>>>
      orderedInputAnchors;
  std::vector<std::map<std::string, uint64_t, std::less<>>>
      orderedInputAnchorEventPositions;
  std::map<std::string, ExactScalarValue, std::less<>> parameters;
  std::vector<ReductionContractRoundValue> rounds;
};

bool operator==(const ReductionContractValue &lhs,
                const ReductionContractValue &rhs);
bool operator!=(const ReductionContractValue &lhs,
                const ReductionContractValue &rhs);

/// Exact path transition selected by a path binding.  The duplex facts are an
/// immutable copy derived from the sealed view; no caller-provided Boolean
/// stands in for authenticated path structure.
struct PathTransitionValue {
  ExactRef ref;
  std::string artifactId;
  ClaimRef claim;
  std::shared_ptr<const SealedDuplexFacts> duplexFacts;
};

bool operator==(const PathTransitionValue &lhs, const PathTransitionValue &rhs);
bool operator!=(const PathTransitionValue &lhs, const PathTransitionValue &rhs);

/// SRS and FRI-domain instances are semantic identities, not registry
/// handles.  Their exact source revisions distinguish otherwise equal names.
struct SrsInstanceValue {
  ExactRef ref;
};

struct FriDomainInstanceValue {
  ExactRef ref;
};

bool operator==(const SrsInstanceValue &lhs, const SrsInstanceValue &rhs);
bool operator!=(const SrsInstanceValue &lhs, const SrsInstanceValue &rhs);
bool operator==(const FriDomainInstanceValue &lhs,
                const FriDomainInstanceValue &rhs);
bool operator!=(const FriDomainInstanceValue &lhs,
                const FriDomainInstanceValue &rhs);

struct SecuritySubject;

/// A typed closed value.  Subject recursion is immutable and explicitly
/// owned so an external-instance subject can contain further typed arguments.
struct RuntimeValue {
  using SubjectPtr = std::shared_ptr<const SecuritySubject>;
  using Payload =
      std::variant<registry::Rational, std::string, bool, SubjectPtr,
                   ReductionContractValue, PathTransitionValue,
                   RoundAdjacencyValue, AlgebraInstanceValue, SrsInstanceValue,
                   FriDomainInstanceValue>;

  ValueSort sort = ValueSort::Rational;
  Payload payload = registry::Rational();

  static RuntimeValue integer(registry::Rational value);
  static RuntimeValue rational(registry::Rational value);
  static RuntimeValue text(std::string value);
  static RuntimeValue boolean(bool value);
  static RuntimeValue subject(SecuritySubject value);
  static RuntimeValue reductionContract(ReductionContractValue value);
  static RuntimeValue pathTransition(PathTransitionValue value);
  static RuntimeValue roundAdjacency(RoundAdjacencyValue value);
  static RuntimeValue algebra(AlgebraInstanceValue value);
  static RuntimeValue srs(SrsInstanceValue value);
  static RuntimeValue friDomain(FriDomainInstanceValue value);
};

bool operator==(const RuntimeValue &lhs, const RuntimeValue &rhs);
bool operator!=(const RuntimeValue &lhs, const RuntimeValue &rhs);

struct ExternalInstanceSubject {
  std::string schemaRef;
  std::vector<RuntimeValue> arguments;
};

bool operator==(const ExternalInstanceSubject &lhs,
                const ExternalInstanceSubject &rhs);
bool operator!=(const ExternalInstanceSubject &lhs,
                const ExternalInstanceSubject &rhs);

struct SecuritySubject {
  using Payload = std::variant<ProtocolClaimSubject, ConsumedClaimVectorSubject,
                               ExternalInstanceSubject>;
  Payload payload = ProtocolClaimSubject();
};

bool operator==(const SecuritySubject &lhs, const SecuritySubject &rhs);
bool operator!=(const SecuritySubject &lhs, const SecuritySubject &rhs);

/// One term coefficient * resource^exponent.  Products of distinct symbolic
/// resources are deliberately absent from the v0 normal form.
struct ResourceMonomial {
  registry::Rational coefficient;
  std::string resource;
  uint64_t exponent = 1;
};

bool operator==(const ResourceMonomial &lhs, const ResourceMonomial &rhs);
bool operator!=(const ResourceMonomial &lhs, const ResourceMonomial &rhs);

/// Canonical graded-linear quantity:
///   constant + sum(coefficient * resource^positive_integer).
///
/// v0 keeps this symbolic: it does not expose a separate valuation API.
/// Resource declarations range over nonnegative exact numeric values, so the
/// nonnegative coefficients checked by runtime well-formedness make this
/// quantity nonnegative at every admitted valuation.  Structural sizes
/// (extraction arities and challenge spaces) are stricter: they must be
/// resource-free positive exact integers.
struct ClosedQuantity {
  registry::Rational constant;
  std::vector<ResourceMonomial> resourceTerms;
};

bool operator==(const ClosedQuantity &lhs, const ClosedQuantity &rhs);
bool operator!=(const ClosedQuantity &lhs, const ClosedQuantity &rhs);

struct PrimitiveGameInstance {
  ExactRef ref;
  std::vector<RuntimeValue> arguments;
};

bool operator==(const PrimitiveGameInstance &lhs,
                const PrimitiveGameInstance &rhs);
bool operator!=(const PrimitiveGameInstance &lhs,
                const PrimitiveGameInstance &rhs);

/// A positive coefficient times one exact primitive-game advantage.  Resource
/// substitutions are closed quantities over the enclosing judgment's
/// declared resources.
struct PrimitiveGameTerm {
  registry::Rational coefficient;
  PrimitiveGameInstance instance;
  std::map<std::string, ClosedQuantity, std::less<>> resourceSubstitution;
};

bool operator==(const PrimitiveGameTerm &lhs, const PrimitiveGameTerm &rhs);
bool operator!=(const PrimitiveGameTerm &lhs, const PrimitiveGameTerm &rhs);

/// The executable v0 normal form: a nonnegative statistical quantity plus a
/// finite sum of positive primitive-game terms.
struct ClosedBound {
  ClosedQuantity quantity;
  std::vector<PrimitiveGameTerm> primitiveGameTerms;
};

bool operator==(const ClosedBound &lhs, const ClosedBound &rhs);
bool operator!=(const ClosedBound &lhs, const ClosedBound &rhs);

/// Result of one exact operation in the executable closed-bound normal form.
/// Arithmetic that would leave that form refuses instead of approximating.
struct ClosedBoundOperationResult {
  std::optional<ClosedBound> value;
  std::optional<SoundnessRefusal> refusal;

  bool accepted() const { return value.has_value() && !refusal.has_value(); }
};

/// Partial exact coefficientwise comparison result.  `false` means the
/// candidate is not coefficientwise dominated by the ceiling; an unsupported
/// or malformed comparison carries a refusal.
struct ClosedBoundComparisonResult {
  std::optional<bool> value;
  std::optional<SoundnessRefusal> refusal;

  bool accepted() const { return value.has_value() && !refusal.has_value(); }
};

ClosedBoundOperationResult closedBoundSpecialize(
    const ClosedBound &bound,
    const std::map<std::string, ClosedQuantity, std::less<>> &substitutions,
    std::string location = "bound.specialize");
ClosedBoundOperationResult closedBoundAdd(const ClosedBound &lhs,
                                          const ClosedBound &rhs,
                                          std::string location = "bound.add");
ClosedBoundOperationResult
closedBoundMaximum(const std::vector<ClosedBound> &bounds,
                   std::string location = "bound.maximum");
ClosedBoundOperationResult
closedBoundScale(const ClosedQuantity &scale, const ClosedBound &bound,
                 std::string location = "bound.scale");
ClosedBoundComparisonResult closedBoundLeq(const ClosedBound &candidate,
                                           const ClosedBound &ceiling,
                                           std::string location = "bound.leq");

struct ExtractionCoordinate {
  std::string label;
  ClosedQuantity arity;
  std::optional<ClosedQuantity> challengeSpace;
};

bool operator==(const ExtractionCoordinate &lhs,
                const ExtractionCoordinate &rhs);
bool operator!=(const ExtractionCoordinate &lhs,
                const ExtractionCoordinate &rhs);

struct ExtractionResult {
  std::vector<ExtractionCoordinate> coordinates;
  std::optional<ClosedBound> failureBound;
};

bool operator==(const ExtractionResult &lhs, const ExtractionResult &rhs);
bool operator!=(const ExtractionResult &lhs, const ExtractionResult &rhs);

/// The state a round-by-round argument tracks, named. Round-by-round
/// soundness is defined over a state function on transcripts
/// (docs/spec/soundness.md §5), and this repository carried the bound
/// machinery without naming the function. The one admitted predicate
/// says the state is doomed exactly when this claim is unsatisfied,
/// which ties a round's bound back to the claim graph instead of
/// leaving the state function implicit.
struct RoundStatePredicate {
  ClaimRef claimUnsatisfied;
};

bool operator==(const RoundStatePredicate &lhs, const RoundStatePredicate &rhs);
bool operator!=(const RoundStatePredicate &lhs, const RoundStatePredicate &rhs);

struct RoundResultEntry {
  std::string roundIndex;
  ClosedQuantity challengeSpace;
  ClosedBound bound;
  /// Present at a reduction occurrence, where the site's owner claim is
  /// the thing the rounds argue; absent — not defaulted — elsewhere,
  /// since a path occurrence consumes no claim to name. Preservation
  /// concatenates entries from different sites, which is why the
  /// predicate lives on the entry rather than on the result.
  std::optional<RoundStatePredicate> statePredicate;
};

bool operator==(const RoundResultEntry &lhs, const RoundResultEntry &rhs);
bool operator!=(const RoundResultEntry &lhs, const RoundResultEntry &rhs);

struct RoundResult {
  std::vector<RoundResultEntry> rounds;
};

bool operator==(const RoundResult &lhs, const RoundResult &rhs);
bool operator!=(const RoundResult &lhs, const RoundResult &rhs);

struct ScalarResult {
  ClosedBound bound;
};

bool operator==(const ScalarResult &lhs, const ScalarResult &rhs);
bool operator!=(const ScalarResult &lhs, const ScalarResult &rhs);

using SecurityResult =
    std::variant<ExtractionResult, RoundResult, ScalarResult>;

bool securityResultEqual(const SecurityResult &lhs, const SecurityResult &rhs);
ResultSchema resultSchemaOf(const SecurityResult &result);

struct PropositionInstance {
  ExactRef ref;
  std::vector<RuntimeValue> arguments;
};

bool operator==(const PropositionInstance &lhs, const PropositionInstance &rhs);
bool operator!=(const PropositionInstance &lhs, const PropositionInstance &rhs);

struct SecurityJudgment;

/// The original closed judgment supplied by an explicit Assume plan leaf.
/// It is semantic input, not an evidence or provenance record.
struct AssumedJudgmentHolds {
  std::shared_ptr<const SecurityJudgment> assertedJudgment;
};

using Hypothesis = std::variant<PropositionInstance, AssumedJudgmentHolds>;

bool hypothesisEqual(const Hypothesis &lhs, const Hypothesis &rhs);

struct SecurityJudgment {
  SecuritySubject subject;
  SecurityIndex index;
  SecurityResult result = ExtractionResult();
  /// Names the nonnegative exact numeric coordinates quantified by this
  /// judgment.  Values are deliberately not stored here: a closed judgment is
  /// interpreted for every well-typed valuation of these declarations.
  std::vector<TypedDeclaration> resourceVariables;
  std::vector<Hypothesis> hypotheses;
};

bool operator==(const SecurityJudgment &lhs, const SecurityJudgment &rhs);
bool operator!=(const SecurityJudgment &lhs, const SecurityJudgment &rhs);

/// Structural checks do not consult registry state or execute a rule.
RuntimeCheckResult checkRuntimeValueWellFormed(const RuntimeValue &value,
                                               std::string location = "value");
RuntimeCheckResult
checkSecuritySubjectWellFormed(const SecuritySubject &subject,
                               std::string location = "subject");
RuntimeCheckResult
checkClosedQuantityWellFormed(const ClosedQuantity &quantity,
                              std::string location = "quantity");
RuntimeCheckResult checkClosedBoundWellFormed(const ClosedBound &bound,
                                              std::string location = "bound");

/// Contextual judgment checking validates exact schema/game/proposition
/// references, typed arguments, resource closure, and index/result agreement.
RuntimeCheckResult
checkSecurityJudgmentWellFormed(const SchemaContext &context,
                                const SecurityJudgment &judgment,
                                std::string location = "judgment");

/// Structural game support, before any resource valuation.  Equal instances
/// are returned once, in first-occurrence order.
std::vector<PrimitiveGameInstance> gameSupport(const SecurityResult &result);

} // namespace zkc::soundness

#endif // ZKC_SOUNDNESS_SOUNDNESSRUNTIME_H
