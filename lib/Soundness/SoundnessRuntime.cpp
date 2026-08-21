//===- SoundnessRuntime.cpp - Owned closed soundness values --------------===//
#include "zkc/Soundness/KernelPredicates.h"
#include "zkc/Soundness/SoundnessRuntime.h"

#include <algorithm>
#include <set>
#include <type_traits>
#include <utility>

namespace zkc::soundness {

namespace {

constexpr int64_t kV0MaxExactExponent = 4096;

bool equalRational(const registry::Rational &lhs,
                   const registry::Rational &rhs) {
  return lhs.compare(rhs) == 0;
}

bool equalOptionalRational(const std::optional<registry::Rational> &lhs,
                           const std::optional<registry::Rational> &rhs) {
  if (lhs.has_value() != rhs.has_value())
    return false;
  return !lhs || equalRational(*lhs, *rhs);
}

bool validChallengeShape(ChallengeShape shape) {
  switch (shape) {
  case ChallengeShape::Scalar:
  case ChallengeShape::Vector:
    return true;
  }
  return false;
}

bool validChallengeSampling(ChallengeSampling sampling) {
  switch (sampling) {
  case ChallengeSampling::Uniform:
  case ChallengeSampling::UniformIndependent:
    return true;
  }
  return false;
}

bool validCodecKind(CodecKind kind) {
  switch (kind) {
  case CodecKind::ModReduce:
  case CodecKind::TupleBijection:
    return true;
  }
  return false;
}

bool validSecurityTrack(SecurityTrack track) {
  switch (track) {
  case SecurityTrack::Soundness:
  case SecurityTrack::Knowledge:
  case SecurityTrack::Completeness:
    return true;
  }
  return false;
}

bool validSecurityIndexShape(const SecurityIndex &index) {
  if (!validSecurityTrack(index.track))
    return false;
  if ((index.notion == SecurityNotion::Completeness) !=
      (index.track == SecurityTrack::Completeness))
    return false;
  switch (index.notion) {
  case SecurityNotion::SpecialSoundness:
  case SecurityNotion::ComputationalSpecialSoundness:
    return index.variant.empty() && index.model.empty();
  case SecurityNotion::RoundByRound:
  case SecurityNotion::StateRestoration:
    return !index.variant.empty() && index.model.empty();
  case SecurityNotion::FiatShamir:
    return !index.variant.empty() && index.model == "duplex";
  case SecurityNotion::Completeness:
    return index.variant.empty() && index.model.empty();
  }
  return false;
}

RuntimeCheckResult accepted() { return {}; }

RuntimeCheckResult refuse(RuntimePhase phase, RuntimeRefusalCode code,
                          std::string location, std::string detail) {
  return RuntimeCheckResult{
      SoundnessRefusal{phase, code, std::move(location), std::move(detail)}};
}

struct EqualityState {
  std::set<std::pair<const SecuritySubject *, const SecuritySubject *>>
      subjectPairs;
  std::set<std::pair<const SecurityJudgment *, const SecurityJudgment *>>
      judgmentPairs;
};

bool runtimeValueEqualImpl(const RuntimeValue &lhs, const RuntimeValue &rhs,
                           EqualityState &state);
bool subjectEqualImpl(const SecuritySubject &lhs, const SecuritySubject &rhs,
                      EqualityState &state);
bool judgmentEqualImpl(const SecurityJudgment &lhs, const SecurityJudgment &rhs,
                       EqualityState &state);

bool runtimeValuesEqual(const std::vector<RuntimeValue> &lhs,
                        const std::vector<RuntimeValue> &rhs,
                        EqualityState &state) {
  if (lhs.size() != rhs.size())
    return false;
  for (size_t index = 0; index < lhs.size(); ++index)
    if (!runtimeValueEqualImpl(lhs[index], rhs[index], state))
      return false;
  return true;
}

bool externalSubjectEqualImpl(const ExternalInstanceSubject &lhs,
                              const ExternalInstanceSubject &rhs,
                              EqualityState &state) {
  return lhs.schemaRef == rhs.schemaRef &&
         runtimeValuesEqual(lhs.arguments, rhs.arguments, state);
}

bool subjectEqualImpl(const SecuritySubject &lhs, const SecuritySubject &rhs,
                      EqualityState &state) {
  if (lhs.payload.index() != rhs.payload.index())
    return false;

  if (const auto *left = std::get_if<ProtocolClaimSubject>(&lhs.payload))
    return *left == std::get<ProtocolClaimSubject>(rhs.payload);
  if (const auto *left = std::get_if<ConsumedClaimVectorSubject>(&lhs.payload))
    return *left == std::get<ConsumedClaimVectorSubject>(rhs.payload);
  return externalSubjectEqualImpl(
      std::get<ExternalInstanceSubject>(lhs.payload),
      std::get<ExternalInstanceSubject>(rhs.payload), state);
}

bool runtimeValueEqualImpl(const RuntimeValue &lhs, const RuntimeValue &rhs,
                           EqualityState &state) {
  if (lhs.sort != rhs.sort || lhs.payload.index() != rhs.payload.index())
    return false;

  if (const auto *left = std::get_if<registry::Rational>(&lhs.payload))
    return equalRational(*left, std::get<registry::Rational>(rhs.payload));
  if (const auto *left = std::get_if<std::string>(&lhs.payload))
    return *left == std::get<std::string>(rhs.payload);
  if (const auto *left = std::get_if<bool>(&lhs.payload))
    return *left == std::get<bool>(rhs.payload);
  if (const auto *left = std::get_if<RuntimeValue::SubjectPtr>(&lhs.payload)) {
    const auto &right = std::get<RuntimeValue::SubjectPtr>(rhs.payload);
    if (!*left || !right)
      return !*left && !right;
    if (left->get() == right.get())
      return true;
    auto pair = std::pair{left->get(), right.get()};
    if (!state.subjectPairs.insert(pair).second)
      return true;
    return subjectEqualImpl(**left, *right, state);
  }
  if (const auto *left = std::get_if<ReductionContractValue>(&lhs.payload))
    return *left == std::get<ReductionContractValue>(rhs.payload);
  if (const auto *left = std::get_if<PathTransitionValue>(&lhs.payload))
    return *left == std::get<PathTransitionValue>(rhs.payload);
  if (const auto *left = std::get_if<RoundAdjacencyValue>(&lhs.payload))
    return *left == std::get<RoundAdjacencyValue>(rhs.payload);
  if (const auto *left = std::get_if<AlgebraInstanceValue>(&lhs.payload))
    return *left == std::get<AlgebraInstanceValue>(rhs.payload);
  if (const auto *left = std::get_if<SrsInstanceValue>(&lhs.payload))
    return *left == std::get<SrsInstanceValue>(rhs.payload);
  return std::get<FriDomainInstanceValue>(lhs.payload) ==
         std::get<FriDomainInstanceValue>(rhs.payload);
}

bool gameInstanceEqualImpl(const PrimitiveGameInstance &lhs,
                           const PrimitiveGameInstance &rhs,
                           EqualityState &state) {
  return lhs.ref == rhs.ref &&
         runtimeValuesEqual(lhs.arguments, rhs.arguments, state);
}

bool gameTermKeyEqual(const PrimitiveGameTerm &lhs,
                      const PrimitiveGameTerm &rhs) {
  EqualityState state;
  return gameInstanceEqualImpl(lhs.instance, rhs.instance, state) &&
         lhs.resourceSubstitution == rhs.resourceSubstitution;
}

bool primitiveTermEqualImpl(const PrimitiveGameTerm &lhs,
                            const PrimitiveGameTerm &rhs,
                            EqualityState &state) {
  return equalRational(lhs.coefficient, rhs.coefficient) &&
         gameInstanceEqualImpl(lhs.instance, rhs.instance, state) &&
         lhs.resourceSubstitution == rhs.resourceSubstitution;
}

bool propositionEqualImpl(const PropositionInstance &lhs,
                          const PropositionInstance &rhs,
                          EqualityState &state) {
  return lhs.ref == rhs.ref &&
         runtimeValuesEqual(lhs.arguments, rhs.arguments, state);
}

bool hypothesisEqualImpl(const Hypothesis &lhs, const Hypothesis &rhs,
                         EqualityState &state) {
  if (lhs.index() != rhs.index())
    return false;
  if (const auto *left = std::get_if<PropositionInstance>(&lhs))
    return propositionEqualImpl(*left, std::get<PropositionInstance>(rhs),
                                state);

  const auto &left = std::get<AssumedJudgmentHolds>(lhs).assertedJudgment;
  const auto &right = std::get<AssumedJudgmentHolds>(rhs).assertedJudgment;
  if (!left || !right)
    return !left && !right;
  if (left.get() == right.get())
    return true;
  auto pair = std::pair{left.get(), right.get()};
  if (!state.judgmentPairs.insert(pair).second)
    return true;
  return judgmentEqualImpl(*left, *right, state);
}

bool hypothesisSetsEqual(const std::vector<Hypothesis> &lhs,
                         const std::vector<Hypothesis> &rhs,
                         EqualityState &state) {
  if (lhs.size() != rhs.size())
    return false;
  std::vector<bool> used(rhs.size(), false);
  for (const Hypothesis &left : lhs) {
    bool matched = false;
    for (size_t index = 0; index < rhs.size(); ++index) {
      if (used[index])
        continue;
      EqualityState candidateState = state;
      if (!hypothesisEqualImpl(left, rhs[index], candidateState))
        continue;
      state = std::move(candidateState);
      used[index] = true;
      matched = true;
      break;
    }
    if (!matched)
      return false;
  }
  return true;
}

bool resultEqualImpl(const SecurityResult &lhs, const SecurityResult &rhs) {
  return securityResultEqual(lhs, rhs);
}

bool judgmentEqualImpl(const SecurityJudgment &lhs, const SecurityJudgment &rhs,
                       EqualityState &state) {
  if (!subjectEqualImpl(lhs.subject, rhs.subject, state) ||
      lhs.index != rhs.index || !resultEqualImpl(lhs.result, rhs.result) ||
      lhs.resourceVariables.size() != rhs.resourceVariables.size())
    return false;
  for (size_t index = 0; index < lhs.resourceVariables.size(); ++index) {
    const TypedDeclaration &left = lhs.resourceVariables[index];
    const TypedDeclaration &right = rhs.resourceVariables[index];
    if (left.name != right.name || left.sort != right.sort)
      return false;
  }
  return hypothesisSetsEqual(lhs.hypotheses, rhs.hypotheses, state);
}

struct CheckState {
  std::set<const SecuritySubject *> activeSubjects;
  std::set<const SecurityJudgment *> activeJudgments;
};

RuntimeCheckResult checkRuntimeValueImpl(const RuntimeValue &value,
                                         const std::string &location,
                                         CheckState &state);
RuntimeCheckResult checkSubjectImpl(const SecuritySubject &subject,
                                    const std::string &location,
                                    CheckState &state);
RuntimeCheckResult checkJudgmentImpl(const SchemaContext &context,
                                     const SecurityJudgment &judgment,
                                     const std::string &location,
                                     CheckState &state);

RuntimeCheckResult checkExactScalar(const ExactScalarValue &value,
                                    const std::string &location) {
  switch (value.sort) {
  case ValueSort::Integer: {
    const auto *number = std::get_if<registry::Rational>(&value.payload);
    if (!number || !isInteger(*number))
      return refuse(RuntimePhase::ValueValidation,
                    RuntimeRefusalCode::SortMismatch, location,
                    "integer field does not carry an exact integer");
    return accepted();
  }
  case ValueSort::Rational:
    if (!std::holds_alternative<registry::Rational>(value.payload))
      return refuse(RuntimePhase::ValueValidation,
                    RuntimeRefusalCode::SortMismatch, location,
                    "rational field does not carry an exact rational");
    return accepted();
  case ValueSort::String:
    if (!std::holds_alternative<std::string>(value.payload))
      return refuse(RuntimePhase::ValueValidation,
                    RuntimeRefusalCode::SortMismatch, location,
                    "string field does not carry a string");
    return accepted();
  case ValueSort::Boolean:
    if (!std::holds_alternative<bool>(value.payload))
      return refuse(RuntimePhase::ValueValidation,
                    RuntimeRefusalCode::SortMismatch, location,
                    "Boolean field does not carry a Boolean");
    return accepted();
  case ValueSort::Subject:
  case ValueSort::ReductionContract:
  case ValueSort::PathTransition:
  case ValueSort::RoundAdjacency:
  case ValueSort::AlgebraInstance:
  case ValueSort::SrsInstance:
  case ValueSort::FriDomainInstance:
    return refuse(RuntimePhase::ValueValidation,
                  RuntimeRefusalCode::SortMismatch, location,
                  "authenticated scalar field has a non-scalar sort");
  }
  return refuse(RuntimePhase::ValueValidation, RuntimeRefusalCode::SortMismatch,
                location, "authenticated scalar field has an unknown sort");
}

RuntimeCheckResult checkNamedScalars(
    const std::map<std::string, ExactScalarValue, std::less<>> &values,
    const std::string &location) {
  for (const auto &[name, value] : values) {
    if (name.empty())
      return refuse(RuntimePhase::ValueValidation,
                    RuntimeRefusalCode::InvalidReference, location,
                    "named scalar field has an empty name");
    RuntimeCheckResult check = checkExactScalar(value, location + "." + name);
    if (!check.accepted())
      return check;
  }
  return accepted();
}

RuntimeCheckResult checkClaim(const ClaimRef &claim,
                              const std::string &location) {
  if (claim.descriptorDigest.empty())
    return refuse(RuntimePhase::SubjectValidation,
                  RuntimeRefusalCode::InvalidReference, location,
                  "claim reference has an empty descriptor digest");
  return accepted();
}

RuntimeCheckResult checkReductionContract(const ReductionContractValue &value,
                                          const std::string &location) {
  if (!validRef(value.ref))
    return refuse(RuntimePhase::ValueValidation,
                  RuntimeRefusalCode::InvalidReference, location,
                  "reduction contract lacks an exact reference or version");
  if (value.inputCount == 0)
    return refuse(RuntimePhase::ValueValidation,
                  RuntimeRefusalCode::EmptyCollection,
                  location + ".input_count",
                  "a soundness reduction contract must consume a claim");
  if (value.rounds.empty())
    return refuse(RuntimePhase::ValueValidation,
                  RuntimeRefusalCode::EmptyCollection, location + ".rounds",
                  "reduction contract has no authenticated rounds");
  if ((!value.orderedInputAnchors.empty() ||
       !value.orderedInputAnchorEventPositions.empty()) &&
      (value.orderedInputAnchors.size() != value.inputCount ||
       value.orderedInputAnchorEventPositions.size() != value.inputCount))
    return refuse(RuntimePhase::ValueValidation,
                  RuntimeRefusalCode::InvalidPayload,
                  location + ".input_anchor_facts",
                  "input-anchor fact vectors must exactly cover every "
                  "consumed claim");
  for (size_t input = 0; input < value.orderedInputAnchors.size(); ++input) {
    const auto &anchors = value.orderedInputAnchors[input];
    const auto &positions = value.orderedInputAnchorEventPositions[input];
    for (const auto &[name, anchor] : anchors)
      if (name.empty() || anchor.empty())
        return refuse(
            RuntimePhase::ValueValidation, RuntimeRefusalCode::InvalidReference,
            location + ".input_anchors[" + std::to_string(input) + "]",
            "input anchor has an empty name or value");
    for (const auto &[name, position] : positions) {
      (void)position;
      if (!anchors.count(name))
        return refuse(RuntimePhase::ValueValidation,
                      RuntimeRefusalCode::InvalidReference,
                      location + ".input_anchor_event_positions[" +
                          std::to_string(input) + "]." + name,
                      "an anchor event position names no exact input anchor");
    }
  }
  RuntimeCheckResult fields =
      checkNamedScalars(value.parameters, location + ".parameters");
  if (!fields.accepted())
    return fields;

  std::set<std::string> indices;
  for (size_t position = 0; position < value.rounds.size(); ++position) {
    const ReductionContractRoundValue &round = value.rounds[position];
    std::string roundLocation =
        location + ".rounds[" + std::to_string(position) + "]";
    if (!isInteger(round.roundIndex) || !isNonnegative(round.roundIndex))
      return refuse(RuntimePhase::ValueValidation,
                    RuntimeRefusalCode::InvalidPayload,
                    roundLocation + ".round_index",
                    "round index must be a nonnegative exact integer");
    if (!indices.insert(round.roundIndex.str()).second)
      return refuse(RuntimePhase::ValueValidation,
                    RuntimeRefusalCode::DuplicateName,
                    roundLocation + ".round_index",
                    "contract round indices must be unique");
    if (round.challengeRole.empty() || round.challengePayloadClass.empty() ||
        round.challengeDomain.empty() ||
        !validChallengeShape(round.challengeShape) ||
        !validChallengeSampling(round.challengeSampling))
      return refuse(RuntimePhase::ValueValidation,
                    RuntimeRefusalCode::InvalidPayload, roundLocation,
                    "contract round has an invalid authenticated challenge");
    if (!isInteger(round.challengeSpace) || !isPositive(round.challengeSpace))
      return refuse(RuntimePhase::ValueValidation,
                    RuntimeRefusalCode::ArithmeticDomain,
                    roundLocation + ".challenge_space",
                    "challenge space must be a positive exact integer");
    if (!isInteger(round.challengeCount) || !isPositive(round.challengeCount))
      return refuse(RuntimePhase::ValueValidation,
                    RuntimeRefusalCode::ArithmeticDomain,
                    roundLocation + ".challenge_count",
                    "challenge count must be a positive exact integer");
    auto count = round.challengeCount.floorToInt();
    if (!count ||
        (round.challengeShape == ChallengeShape::Scalar &&
         (*count != 1 ||
          round.challengeSampling != ChallengeSampling::Uniform)) ||
        (round.challengeShape == ChallengeShape::Vector &&
         (*count < 2 ||
          round.challengeSampling != ChallengeSampling::UniformIndependent)))
      return refuse(RuntimePhase::ValueValidation,
                    RuntimeRefusalCode::InvalidPayload, roundLocation,
                    "challenge shape, count, and sampling disagree");
    std::set<std::string> messageRoles;
    for (const SealedMessageRoleFact &message : round.messages) {
      if (message.role.empty() || !messageRoles.insert(message.role).second ||
          message.payloadClassesByOccurrence.empty() ||
          std::any_of(message.payloadClassesByOccurrence.begin(),
                      message.payloadClassesByOccurrence.end(),
                      [](const std::string &payloadClass) {
                        return payloadClass.empty();
                      }))
        return refuse(RuntimePhase::ValueValidation,
                      RuntimeRefusalCode::InvalidPayload,
                      roundLocation + ".messages",
                      "contract round has an invalid message-role fact");
    }
    if (round.roundDegree &&
        (!isInteger(*round.roundDegree) || !isNonnegative(*round.roundDegree)))
      return refuse(RuntimePhase::ValueValidation,
                    RuntimeRefusalCode::ArithmeticDomain,
                    roundLocation + ".round_degree",
                    "round degree must be a nonnegative exact integer");
    if (round.challengeSpaceLog2) {
      if (!isInteger(*round.challengeSpaceLog2) ||
          !isNonnegative(*round.challengeSpaceLog2))
        return refuse(RuntimePhase::ValueValidation,
                      RuntimeRefusalCode::ArithmeticDomain,
                      roundLocation + ".challenge_space_log2",
                      "challenge-space log2 must be a nonnegative integer");
      auto exponent = round.challengeSpaceLog2->floorToInt();
      if (!exponent)
        return refuse(RuntimePhase::ValueValidation,
                      RuntimeRefusalCode::UnsupportedNormalForm,
                      roundLocation + ".challenge_space_log2",
                      "challenge-space log2 exceeds the exact exponent domain");
      if (*exponent > kV0MaxExactExponent)
        return refuse(RuntimePhase::ValueValidation,
                      RuntimeRefusalCode::UnsupportedNormalForm,
                      roundLocation + ".challenge_space_log2",
                      "challenge-space log2 exceeds the v0 exact range");
      auto reconstructed = registry::Rational::fromInteger(2).pow(*exponent);
      if (!reconstructed ||
          !equalRational(*reconstructed, round.challengeSpace))
        return refuse(RuntimePhase::ValueValidation,
                      RuntimeRefusalCode::InvalidPayload,
                      roundLocation + ".challenge_space_log2",
                      "challenge-space log2 disagrees with challenge space");
    }
  }
  return accepted();
}

RuntimeCheckResult checkPathTransition(const PathTransitionValue &value,
                                       const std::string &location) {
  if (!validRef(value.ref) || value.artifactId.empty())
    return refuse(RuntimePhase::ValueValidation,
                  RuntimeRefusalCode::InvalidReference, location,
                  "path transition lacks an exact reference or artifact id");
  RuntimeCheckResult claim = checkClaim(value.claim, location + ".claim");
  if (!claim.accepted())
    return claim;
  if (!value.duplexFacts)
    return accepted();

  const SealedDuplexFacts &facts = *value.duplexFacts;
  if (!validRef(facts.spongeRef) || !isInteger(facts.alphabetOrder) ||
      !isPositive(facts.alphabetOrder) || facts.capacity == 0 ||
      facts.rate == 0)
    return refuse(RuntimePhase::ValueValidation,
                  RuntimeRefusalCode::InvalidPayload,
                  location + ".duplex_facts",
                  "sealed duplex facts have an invalid exact carrier");
  if (!std::is_sorted(facts.segmentStarts.begin(), facts.segmentStarts.end()) ||
      std::adjacent_find(facts.segmentStarts.begin(),
                         facts.segmentStarts.end()) !=
          facts.segmentStarts.end())
    return refuse(RuntimePhase::ValueValidation,
                  RuntimeRefusalCode::InvalidPayload,
                  location + ".duplex_facts.segment_starts",
                  "duplex segment starts must be unique and ordered");
  if (!isNonnegative(facts.codecBiasMax) || !isNonnegative(facts.codecBiasSum))
    return refuse(RuntimePhase::ValueValidation,
                  RuntimeRefusalCode::ArithmeticDomain,
                  location + ".duplex_facts",
                  "duplex codec-bias values must be nonnegative");
  uint64_t previousEvent = 0;
  bool hasPreviousEvent = false;
  registry::Rational recomputedMax;
  registry::Rational recomputedSum;
  for (size_t index = 0; index < facts.challenges.size(); ++index) {
    const SealedChallengeCodecFact &challenge = facts.challenges[index];
    std::string challengeLocation =
        location + ".duplex_facts.challenges[" + std::to_string(index) + "]";
    if ((hasPreviousEvent && challenge.eventPosition <= previousEvent) ||
        challenge.payloadClass.empty() || challenge.domain.empty() ||
        !isInteger(challenge.space) || !isPositive(challenge.space) ||
        challenge.count == 0 || !validRef(challenge.codecRef) ||
        !validChallengeShape(challenge.shape) ||
        !validChallengeSampling(challenge.sampling) ||
        !validCodecKind(challenge.codecKind) || challenge.squeezeSymbols == 0 ||
        !isNonnegative(challenge.biasContribution))
      return refuse(RuntimePhase::ValueValidation,
                    RuntimeRefusalCode::InvalidPayload, challengeLocation,
                    "sealed challenge-codec fact is not an exact ordered "
                    "positive-domain event");
    if ((challenge.shape == ChallengeShape::Scalar &&
         (challenge.count != 1 ||
          challenge.sampling != ChallengeSampling::Uniform)) ||
        (challenge.shape == ChallengeShape::Vector &&
         (challenge.count < 2 ||
          challenge.sampling != ChallengeSampling::UniformIndependent)))
      return refuse(RuntimePhase::ValueValidation,
                    RuntimeRefusalCode::InvalidPayload, challengeLocation,
                    "challenge shape, count, and sampling disagree");
    previousEvent = challenge.eventPosition;
    hasPreviousEvent = true;
    if (recomputedMax.compare(challenge.biasContribution) < 0)
      recomputedMax = challenge.biasContribution;
    recomputedSum = recomputedSum.add(challenge.biasContribution);
  }
  if (!equalRational(recomputedMax, facts.codecBiasMax) ||
      !equalRational(recomputedSum, facts.codecBiasSum))
    return refuse(RuntimePhase::ValueValidation,
                  RuntimeRefusalCode::InvalidPayload,
                  location + ".duplex_facts",
                  "duplex codec-bias aggregates do not equal the exact "
                  "challenge contributions");
  return accepted();
}

RuntimeCheckResult checkRoundAdjacency(const RoundAdjacencyValue &value,
                                       const std::string &location) {
  if (!validRef(value.contractRef))
    return refuse(RuntimePhase::ValueValidation,
                  RuntimeRefusalCode::InvalidReference, location,
                  "round adjacency lacks an exact contract reference");
  return checkClaim(value.premiseClaim, location + ".premise_claim");
}

RuntimeCheckResult checkSubjectImpl(const SecuritySubject &subject,
                                    const std::string &location,
                                    CheckState &state) {
  if (const auto *protocol =
          std::get_if<ProtocolClaimSubject>(&subject.payload)) {
    if (protocol->artifactId.empty())
      return refuse(RuntimePhase::SubjectValidation,
                    RuntimeRefusalCode::InvalidReference, location,
                    "protocol-claim subject has an empty artifact id");
    return checkClaim(protocol->claim, location + ".claim");
  }

  if (const auto *consumed =
          std::get_if<ConsumedClaimVectorSubject>(&subject.payload)) {
    if (consumed->artifactId.empty())
      return refuse(RuntimePhase::SubjectValidation,
                    RuntimeRefusalCode::InvalidReference, location,
                    "consumed-claim subject has an empty artifact id");
    RuntimeCheckResult consumer =
        checkClaim(consumed->consumer, location + ".consumer");
    if (!consumer.accepted())
      return consumer;
    if (consumed->orderedSources.empty())
      return refuse(RuntimePhase::SubjectValidation,
                    RuntimeRefusalCode::EmptyCollection,
                    location + ".ordered_sources",
                    "consumed-claim subject has no source claims");
    for (size_t index = 0; index < consumed->orderedSources.size(); ++index) {
      RuntimeCheckResult source = checkClaim(consumed->orderedSources[index],
                                             location + ".ordered_sources[" +
                                                 std::to_string(index) + "]");
      if (!source.accepted())
        return source;
    }
    return accepted();
  }

  const ExternalInstanceSubject &external =
      std::get<ExternalInstanceSubject>(subject.payload);
  if (external.schemaRef.empty())
    return refuse(RuntimePhase::SubjectValidation,
                  RuntimeRefusalCode::InvalidReference,
                  location + ".schema_ref",
                  "external-instance subject has an empty schema reference");
  if (external.arguments.empty())
    return refuse(RuntimePhase::SubjectValidation,
                  RuntimeRefusalCode::EmptyCollection, location + ".arguments",
                  "external-instance subject has no typed arguments");
  for (size_t index = 0; index < external.arguments.size(); ++index) {
    RuntimeCheckResult argument = checkRuntimeValueImpl(
        external.arguments[index],
        location + ".arguments[" + std::to_string(index) + "]", state);
    if (!argument.accepted())
      return argument;
  }
  return accepted();
}

RuntimeCheckResult checkRuntimeValueImpl(const RuntimeValue &value,
                                         const std::string &location,
                                         CheckState &state) {
  auto wrongPayload = [&] {
    return refuse(RuntimePhase::ValueValidation,
                  RuntimeRefusalCode::SortMismatch, location,
                  "runtime payload does not match its declared sort");
  };

  switch (value.sort) {
  case ValueSort::Integer: {
    const auto *number = std::get_if<registry::Rational>(&value.payload);
    if (!number || !isInteger(*number))
      return wrongPayload();
    return accepted();
  }
  case ValueSort::Rational:
    return std::holds_alternative<registry::Rational>(value.payload)
               ? accepted()
               : wrongPayload();
  case ValueSort::String:
    return std::holds_alternative<std::string>(value.payload) ? accepted()
                                                              : wrongPayload();
  case ValueSort::Boolean:
    return std::holds_alternative<bool>(value.payload) ? accepted()
                                                       : wrongPayload();
  case ValueSort::Subject: {
    const auto *subject = std::get_if<RuntimeValue::SubjectPtr>(&value.payload);
    if (!subject)
      return wrongPayload();
    if (!*subject)
      return refuse(RuntimePhase::SubjectValidation,
                    RuntimeRefusalCode::NullRecursiveValue, location,
                    "subject payload is null");
    if (!state.activeSubjects.insert(subject->get()).second)
      return refuse(RuntimePhase::SubjectValidation,
                    RuntimeRefusalCode::RecursiveCycle, location,
                    "subject graph contains a recursive cycle");
    RuntimeCheckResult result = checkSubjectImpl(**subject, location, state);
    state.activeSubjects.erase(subject->get());
    return result;
  }
  case ValueSort::ReductionContract: {
    const auto *contract = std::get_if<ReductionContractValue>(&value.payload);
    return contract ? checkReductionContract(*contract, location)
                    : wrongPayload();
  }
  case ValueSort::PathTransition: {
    const auto *path = std::get_if<PathTransitionValue>(&value.payload);
    return path ? checkPathTransition(*path, location) : wrongPayload();
  }
  case ValueSort::RoundAdjacency: {
    const auto *adjacency = std::get_if<RoundAdjacencyValue>(&value.payload);
    return adjacency ? checkRoundAdjacency(*adjacency, location)
                     : wrongPayload();
  }
  case ValueSort::AlgebraInstance: {
    const auto *algebra = std::get_if<AlgebraInstanceValue>(&value.payload);
    if (!algebra)
      return wrongPayload();
    if (algebra->group.empty() || algebra->fieldClass.empty() ||
        !isInteger(algebra->fieldOrder) || !isPositive(algebra->fieldOrder))
      return refuse(RuntimePhase::ValueValidation,
                    RuntimeRefusalCode::InvalidPayload, location,
                    "algebra instance is not an exact positive-order carrier");
    return accepted();
  }
  case ValueSort::SrsInstance: {
    const auto *srs = std::get_if<SrsInstanceValue>(&value.payload);
    if (!srs)
      return wrongPayload();
    return validRef(srs->ref)
               ? accepted()
               : refuse(RuntimePhase::ValueValidation,
                        RuntimeRefusalCode::InvalidReference, location,
                        "SRS instance lacks an exact reference");
  }
  case ValueSort::FriDomainInstance: {
    const auto *domain = std::get_if<FriDomainInstanceValue>(&value.payload);
    if (!domain)
      return wrongPayload();
    return validRef(domain->ref)
               ? accepted()
               : refuse(RuntimePhase::ValueValidation,
                        RuntimeRefusalCode::InvalidReference, location,
                        "FRI-domain instance lacks an exact reference");
  }
  }
  return wrongPayload();
}

RuntimeCheckResult checkQuantityImpl(const ClosedQuantity &quantity,
                                     const std::string &location) {
  if (!isNonnegative(quantity.constant))
    return refuse(RuntimePhase::QuantityValidation,
                  RuntimeRefusalCode::UnsupportedNormalForm,
                  location + ".constant",
                  "closed normal form has a negative constant");

  std::pair<std::string, uint64_t> previous;
  bool hasPrevious = false;
  for (size_t index = 0; index < quantity.resourceTerms.size(); ++index) {
    const ResourceMonomial &term = quantity.resourceTerms[index];
    std::string termLocation =
        location + ".resource_terms[" + std::to_string(index) + "]";
    if (term.resource.empty())
      return refuse(RuntimePhase::QuantityValidation,
                    RuntimeRefusalCode::InvalidResource,
                    termLocation + ".resource",
                    "resource monomial has an empty resource name");
    if (!isPositive(term.coefficient))
      return refuse(RuntimePhase::QuantityValidation,
                    RuntimeRefusalCode::UnsupportedNormalForm,
                    termLocation + ".coefficient",
                    "resource monomial coefficient must be positive");
    if (term.exponent == 0)
      return refuse(RuntimePhase::QuantityValidation,
                    RuntimeRefusalCode::NonCanonicalNormalForm,
                    termLocation + ".exponent",
                    "resource monomial exponent must be positive");
    if (term.exponent > static_cast<uint64_t>(kV0MaxExactExponent))
      return refuse(RuntimePhase::QuantityValidation,
                    RuntimeRefusalCode::UnsupportedNormalForm,
                    termLocation + ".exponent",
                    "resource monomial exponent exceeds the v0 exact range");
    std::pair<std::string, uint64_t> key{term.resource, term.exponent};
    if (hasPrevious && !(previous < key))
      return refuse(RuntimePhase::QuantityValidation,
                    RuntimeRefusalCode::NonCanonicalNormalForm, termLocation,
                    "resource monomials must be strictly ordered and merged");
    previous = std::move(key);
    hasPrevious = true;
  }
  return accepted();
}

RuntimeCheckResult
checkPrimitiveInstanceStructural(const PrimitiveGameInstance &instance,
                                 const std::string &location,
                                 CheckState &state) {
  if (!validRef(instance.ref))
    return refuse(RuntimePhase::BoundValidation,
                  RuntimeRefusalCode::InvalidReference, location,
                  "primitive-game instance lacks an exact reference");
  for (size_t index = 0; index < instance.arguments.size(); ++index) {
    RuntimeCheckResult argument = checkRuntimeValueImpl(
        instance.arguments[index],
        location + ".arguments[" + std::to_string(index) + "]", state);
    if (!argument.accepted())
      return argument;
  }
  return accepted();
}

RuntimeCheckResult checkBoundImpl(const ClosedBound &bound,
                                  const std::string &location,
                                  CheckState &state) {
  RuntimeCheckResult quantity =
      checkQuantityImpl(bound.quantity, location + ".quantity");
  if (!quantity.accepted())
    return quantity;

  for (size_t index = 0; index < bound.primitiveGameTerms.size(); ++index) {
    const PrimitiveGameTerm &term = bound.primitiveGameTerms[index];
    std::string termLocation =
        location + ".primitive_game_terms[" + std::to_string(index) + "]";
    if (!isPositive(term.coefficient))
      return refuse(RuntimePhase::BoundValidation,
                    RuntimeRefusalCode::UnsupportedNormalForm,
                    termLocation + ".coefficient",
                    "primitive-game coefficient must be positive");
    RuntimeCheckResult instance = checkPrimitiveInstanceStructural(
        term.instance, termLocation + ".instance", state);
    if (!instance.accepted())
      return instance;
    for (const auto &[resource, substitution] : term.resourceSubstitution) {
      if (resource.empty())
        return refuse(RuntimePhase::BoundValidation,
                      RuntimeRefusalCode::InvalidResource,
                      termLocation + ".resource_substitution",
                      "primitive-game resource name is empty");
      RuntimeCheckResult substitutionCheck = checkQuantityImpl(
          substitution, termLocation + ".resource_substitution." + resource);
      if (!substitutionCheck.accepted())
        return substitutionCheck;
    }
    for (size_t previous = 0; previous < index; ++previous)
      if (gameTermKeyEqual(bound.primitiveGameTerms[previous], term))
        return refuse(RuntimePhase::BoundValidation,
                      RuntimeRefusalCode::NonCanonicalNormalForm, termLocation,
                      "equal primitive-game terms must be merged");
  }
  return accepted();
}

RuntimeCheckResult
checkPositiveStructuralQuantity(const ClosedQuantity &quantity,
                                const std::string &location,
                                const char *description) {
  RuntimeCheckResult structural = checkQuantityImpl(quantity, location);
  if (!structural.accepted())
    return structural;
  if (!quantity.resourceTerms.empty())
    return refuse(RuntimePhase::ResultValidation,
                  RuntimeRefusalCode::UnsupportedNormalForm, location,
                  std::string(description) +
                      " must not depend on a resource valuation");
  if (!isInteger(quantity.constant) || !isPositive(quantity.constant))
    return refuse(RuntimePhase::ResultValidation,
                  RuntimeRefusalCode::ArithmeticDomain, location,
                  std::string(description) +
                      " must be a positive exact integer");
  return accepted();
}

RuntimeCheckResult checkResultStructural(const SecurityResult &result,
                                         const std::string &location,
                                         CheckState &state) {
  if (const auto *extraction = std::get_if<ExtractionResult>(&result)) {
    if (extraction->coordinates.empty())
      return refuse(
          RuntimePhase::ResultValidation, RuntimeRefusalCode::EmptyCollection,
          location + ".coordinates", "extraction result has no coordinates");
    std::set<std::string> labels;
    for (size_t index = 0; index < extraction->coordinates.size(); ++index) {
      const ExtractionCoordinate &coordinate = extraction->coordinates[index];
      std::string coordinateLocation =
          location + ".coordinates[" + std::to_string(index) + "]";
      if (coordinate.label.empty() || !labels.insert(coordinate.label).second)
        return refuse(RuntimePhase::ResultValidation,
                      RuntimeRefusalCode::DuplicateName,
                      coordinateLocation + ".label",
                      "extraction-coordinate labels must be nonempty and "
                      "unique");
      RuntimeCheckResult arity = checkPositiveStructuralQuantity(
          coordinate.arity, coordinateLocation + ".arity", "extraction arity");
      if (!arity.accepted())
        return arity;
      if (coordinate.challengeSpace) {
        RuntimeCheckResult space = checkPositiveStructuralQuantity(
            *coordinate.challengeSpace, coordinateLocation + ".challenge_space",
            "challenge space");
        if (!space.accepted())
          return space;
      }
    }
    if (extraction->failureBound)
      return checkBoundImpl(*extraction->failureBound,
                            location + ".failure_bound", state);
    return accepted();
  }

  if (const auto *rounds = std::get_if<RoundResult>(&result)) {
    if (rounds->rounds.empty())
      return refuse(RuntimePhase::ResultValidation,
                    RuntimeRefusalCode::EmptyCollection, location + ".rounds",
                    "round result has no rounds");
    std::set<std::string> indices;
    for (size_t index = 0; index < rounds->rounds.size(); ++index) {
      const RoundResultEntry &round = rounds->rounds[index];
      std::string roundLocation =
          location + ".rounds[" + std::to_string(index) + "]";
      if (round.roundIndex.empty() || !indices.insert(round.roundIndex).second)
        return refuse(RuntimePhase::ResultValidation,
                      RuntimeRefusalCode::DuplicateName,
                      roundLocation + ".round_index",
                      "result round indices must be nonempty and unique");
      RuntimeCheckResult space = checkPositiveStructuralQuantity(
          round.challengeSpace, roundLocation + ".challenge_space",
          "challenge space");
      if (!space.accepted())
        return space;
      RuntimeCheckResult bound =
          checkBoundImpl(round.bound, roundLocation + ".bound", state);
      if (!bound.accepted())
        return bound;
    }
    return accepted();
  }

  return checkBoundImpl(std::get<ScalarResult>(result).bound,
                        location + ".bound", state);
}

using ResourceTypes = std::map<std::string, ValueSort, std::less<>>;

RuntimeCheckResult
checkQuantityResources(const ClosedQuantity &quantity,
                       const ResourceTypes &resources,
                       const std::string &location,
                       std::optional<ValueSort> expected = std::nullopt) {
  if (expected == ValueSort::Integer && !isInteger(quantity.constant))
    return refuse(RuntimePhase::QuantityValidation,
                  RuntimeRefusalCode::SortMismatch, location,
                  "integer-valued quantity has a fractional constant");
  for (size_t index = 0; index < quantity.resourceTerms.size(); ++index) {
    const ResourceMonomial &term = quantity.resourceTerms[index];
    auto resource = resources.find(term.resource);
    if (resource == resources.end())
      return refuse(RuntimePhase::QuantityValidation,
                    RuntimeRefusalCode::InvalidResource,
                    location + ".resource_terms[" + std::to_string(index) + "]",
                    "quantity contains an undeclared resource variable");
    if (expected == ValueSort::Integer &&
        (resource->second != ValueSort::Integer ||
         !isInteger(term.coefficient)))
      return refuse(RuntimePhase::QuantityValidation,
                    RuntimeRefusalCode::SortMismatch,
                    location + ".resource_terms[" + std::to_string(index) + "]",
                    "integer-valued quantity contains a fractional source");
  }
  return accepted();
}

RuntimeCheckResult
checkRuntimeArgumentSorts(const std::vector<RuntimeValue> &arguments,
                          const std::vector<ValueSort> &expected,
                          const std::string &location) {
  if (arguments.size() != expected.size())
    return refuse(RuntimePhase::ValueValidation,
                  RuntimeRefusalCode::SortMismatch, location,
                  "typed argument count does not match its schema");
  for (size_t index = 0; index < arguments.size(); ++index)
    if (arguments[index].sort != expected[index])
      return refuse(RuntimePhase::ValueValidation,
                    RuntimeRefusalCode::SortMismatch,
                    location + "[" + std::to_string(index) + "]",
                    "typed argument has the wrong schema sort");
  return accepted();
}

RuntimeCheckResult checkSubjectContext(const SchemaContext &context,
                                       const SecuritySubject &subject,
                                       const std::string &location) {
  constexpr const char *kProtocolClaimSchema = "zkc.subject.protocol_claim";
  constexpr const char *kConsumedClaimVectorSchema =
      "zkc.subject.consumed_claim_vector";

  std::string schemaRef;
  SubjectSchemaKind expectedKind;
  const std::vector<RuntimeValue> *arguments = nullptr;
  if (std::holds_alternative<ProtocolClaimSubject>(subject.payload)) {
    schemaRef = kProtocolClaimSchema;
    expectedKind = SubjectSchemaKind::ProtocolClaim;
  } else if (std::holds_alternative<ConsumedClaimVectorSubject>(
                 subject.payload)) {
    schemaRef = kConsumedClaimVectorSchema;
    expectedKind = SubjectSchemaKind::ConsumedClaimVector;
  } else {
    const ExternalInstanceSubject &external =
        std::get<ExternalInstanceSubject>(subject.payload);
    schemaRef = external.schemaRef;
    expectedKind = SubjectSchemaKind::ExternalInstance;
    arguments = &external.arguments;
  }

  auto schema = context.subjectSchemas.find(schemaRef);
  if (schema == context.subjectSchemas.end() ||
      schema->second.ref != schemaRef || schema->second.kind != expectedKind)
    return refuse(RuntimePhase::SubjectValidation,
                  RuntimeRefusalCode::UnknownSchema, location,
                  "subject names no exact admitted schema of its kind");
  if (!arguments) {
    if (!schema->second.argumentTypes.empty())
      return refuse(RuntimePhase::SubjectValidation,
                    RuntimeRefusalCode::SortMismatch, location,
                    "protocol subject schema unexpectedly requires arguments");
    return accepted();
  }
  return checkRuntimeArgumentSorts(*arguments, schema->second.argumentTypes,
                                   location + ".arguments");
}

RuntimeCheckResult checkGameTermContext(const SchemaContext &context,
                                        const PrimitiveGameTerm &term,
                                        const ResourceTypes &resources,
                                        const std::string &location) {
  auto definition = context.primitiveGames.find(term.instance.ref.id);
  if (definition == context.primitiveGames.end() ||
      definition->second.ref != term.instance.ref)
    return refuse(RuntimePhase::BoundValidation,
                  RuntimeRefusalCode::InvalidPrimitiveGame,
                  location + ".instance",
                  "primitive-game instance names no exact admitted game");
  RuntimeCheckResult arguments = checkRuntimeArgumentSorts(
      term.instance.arguments, definition->second.instanceArgumentTypes,
      location + ".instance.arguments");
  if (!arguments.accepted())
    return arguments;

  const std::vector<TypedDeclaration> &gameResources =
      definition->second.resources;
  std::set<std::string> expectedResources;
  for (const TypedDeclaration &resource : gameResources) {
    if (resource.name.empty() ||
        !expectedResources.insert(resource.name).second ||
        (resource.sort != ValueSort::Integer &&
         resource.sort != ValueSort::Rational))
      return refuse(RuntimePhase::BoundValidation,
                    RuntimeRefusalCode::InvalidResource,
                    location + ".resource_substitution",
                    "each primitive-game resource declaration must have a "
                    "nonempty unique name and numeric sort");
  }
  std::set<std::string> actualResources;
  for (const auto &[name, value] : term.resourceSubstitution) {
    (void)value;
    actualResources.insert(name);
  }
  if (actualResources != expectedResources)
    return refuse(RuntimePhase::BoundValidation,
                  RuntimeRefusalCode::InvalidResource,
                  location + ".resource_substitution",
                  "primitive-game resource substitution keys do not exactly "
                  "match the resource schema");

  for (const TypedDeclaration &resource : gameResources) {
    const ClosedQuantity &substitution =
        term.resourceSubstitution.find(resource.name)->second;
    RuntimeCheckResult quantity = checkQuantityResources(
        substitution, resources,
        location + ".resource_substitution." + resource.name, resource.sort);
    if (!quantity.accepted())
      return quantity;
  }
  return accepted();
}

RuntimeCheckResult checkBoundContext(const SchemaContext &context,
                                     const ClosedBound &bound,
                                     const ResourceTypes &resources,
                                     const std::string &location) {
  RuntimeCheckResult quantity =
      checkQuantityResources(bound.quantity, resources, location + ".quantity");
  if (!quantity.accepted())
    return quantity;
  for (size_t index = 0; index < bound.primitiveGameTerms.size(); ++index) {
    RuntimeCheckResult term = checkGameTermContext(
        context, bound.primitiveGameTerms[index], resources,
        location + ".primitive_game_terms[" + std::to_string(index) + "]");
    if (!term.accepted())
      return term;
  }
  return accepted();
}

RuntimeCheckResult checkResultContext(const SchemaContext &context,
                                      const SecurityResult &result,
                                      const ResourceTypes &resources,
                                      const std::string &location) {
  if (const auto *extraction = std::get_if<ExtractionResult>(&result)) {
    for (size_t index = 0; index < extraction->coordinates.size(); ++index) {
      const ExtractionCoordinate &coordinate = extraction->coordinates[index];
      std::string coordinateLocation =
          location + ".coordinates[" + std::to_string(index) + "]";
      RuntimeCheckResult arity = checkQuantityResources(
          coordinate.arity, resources, coordinateLocation + ".arity",
          ValueSort::Integer);
      if (!arity.accepted())
        return arity;
      if (coordinate.challengeSpace) {
        RuntimeCheckResult space = checkQuantityResources(
            *coordinate.challengeSpace, resources,
            coordinateLocation + ".challenge_space", ValueSort::Integer);
        if (!space.accepted())
          return space;
      }
    }
    if (extraction->failureBound)
      return checkBoundContext(context, *extraction->failureBound, resources,
                               location + ".failure_bound");
    return accepted();
  }

  if (const auto *rounds = std::get_if<RoundResult>(&result)) {
    for (size_t index = 0; index < rounds->rounds.size(); ++index) {
      const RoundResultEntry &round = rounds->rounds[index];
      std::string roundLocation =
          location + ".rounds[" + std::to_string(index) + "]";
      RuntimeCheckResult space = checkQuantityResources(
          round.challengeSpace, resources, roundLocation + ".challenge_space",
          ValueSort::Integer);
      if (!space.accepted())
        return space;
      RuntimeCheckResult bound = checkBoundContext(
          context, round.bound, resources, roundLocation + ".bound");
      if (!bound.accepted())
        return bound;
    }
    return accepted();
  }

  return checkBoundContext(context, std::get<ScalarResult>(result).bound,
                           resources, location + ".bound");
}

RuntimeCheckResult
checkPropositionContext(const SchemaContext &context,
                        const PropositionInstance &proposition,
                        const std::string &location, CheckState &state) {
  if (!validRef(proposition.ref))
    return refuse(RuntimePhase::HypothesisValidation,
                  RuntimeRefusalCode::InvalidReference, location,
                  "proposition instance lacks an exact reference");
  auto schema = context.propositions.find(proposition.ref.id);
  if (schema == context.propositions.end() ||
      schema->second.ref != proposition.ref)
    return refuse(RuntimePhase::HypothesisValidation,
                  RuntimeRefusalCode::InvalidProposition, location,
                  "proposition instance names no exact admitted schema");
  RuntimeCheckResult types = checkRuntimeArgumentSorts(
      proposition.arguments, schema->second.argumentTypes,
      location + ".arguments");
  if (!types.accepted())
    return types;
  for (size_t index = 0; index < proposition.arguments.size(); ++index) {
    RuntimeCheckResult argument = checkRuntimeValueImpl(
        proposition.arguments[index],
        location + ".arguments[" + std::to_string(index) + "]", state);
    if (!argument.accepted())
      return argument;
  }
  return accepted();
}

RuntimeCheckResult checkJudgmentImpl(const SchemaContext &context,
                                     const SecurityJudgment &judgment,
                                     const std::string &location,
                                     CheckState &state) {
  RuntimeCheckResult subject =
      checkSubjectImpl(judgment.subject, location + ".subject", state);
  if (!subject.accepted())
    return subject;
  RuntimeCheckResult subjectContext =
      checkSubjectContext(context, judgment.subject, location + ".subject");
  if (!subjectContext.accepted())
    return subjectContext;

  if (!validSecurityIndexShape(judgment.index))
    return refuse(RuntimePhase::JudgmentValidation,
                  RuntimeRefusalCode::UnknownIndex, location + ".index",
                  "judgment has an unknown security-index enum or malformed "
                  "variant/model shape");
  if (std::find(context.securityIndices.begin(), context.securityIndices.end(),
                judgment.index) == context.securityIndices.end())
    return refuse(RuntimePhase::JudgmentValidation,
                  RuntimeRefusalCode::UnknownIndex, location + ".index",
                  "judgment uses no admitted security index");

  ResultSchema expected = ResultSchema::Extraction;
  switch (judgment.index.notion) {
  case SecurityNotion::SpecialSoundness:
  case SecurityNotion::ComputationalSpecialSoundness:
    expected = ResultSchema::Extraction;
    break;
  case SecurityNotion::RoundByRound:
    expected = ResultSchema::Round;
    break;
  case SecurityNotion::StateRestoration:
  case SecurityNotion::FiatShamir:
  case SecurityNotion::Completeness:
    expected = ResultSchema::Scalar;
    break;
  }
  if (resultSchemaOf(judgment.result) != expected)
    return refuse(RuntimePhase::JudgmentValidation,
                  RuntimeRefusalCode::InvalidResultSchema, location + ".result",
                  "security index and result schema disagree");
  const auto *extraction = std::get_if<ExtractionResult>(&judgment.result);
  if (judgment.index.notion == SecurityNotion::SpecialSoundness &&
      extraction->failureBound)
    return refuse(RuntimePhase::JudgmentValidation,
                  RuntimeRefusalCode::InvalidResultSchema,
                  location + ".result.failure_bound",
                  "special-soundness result cannot carry a failure bound");
  if (judgment.index.notion == SecurityNotion::ComputationalSpecialSoundness &&
      !extraction->failureBound)
    return refuse(RuntimePhase::JudgmentValidation,
                  RuntimeRefusalCode::InvalidResultSchema,
                  location + ".result.failure_bound",
                  "computational special soundness requires a failure bound");

  ResourceTypes resources;
  for (size_t index = 0; index < judgment.resourceVariables.size(); ++index) {
    const TypedDeclaration &resource = judgment.resourceVariables[index];
    if (resource.name.empty() || (resource.sort != ValueSort::Integer &&
                                  resource.sort != ValueSort::Rational))
      return refuse(
          RuntimePhase::JudgmentValidation, RuntimeRefusalCode::InvalidResource,
          location + ".resource_variables[" + std::to_string(index) + "]",
          "judgment resource must be a named numeric declaration");
    if (!resources.emplace(resource.name, resource.sort).second)
      return refuse(
          RuntimePhase::JudgmentValidation, RuntimeRefusalCode::DuplicateName,
          location + ".resource_variables[" + std::to_string(index) + "]",
          "judgment resource names must be unique");
  }

  RuntimeCheckResult structuralResult =
      checkResultStructural(judgment.result, location + ".result", state);
  if (!structuralResult.accepted())
    return structuralResult;
  RuntimeCheckResult contextualResult = checkResultContext(
      context, judgment.result, resources, location + ".result");
  if (!contextualResult.accepted())
    return contextualResult;

  for (size_t index = 0; index < judgment.hypotheses.size(); ++index) {
    const Hypothesis &hypothesis = judgment.hypotheses[index];
    std::string hypothesisLocation =
        location + ".hypotheses[" + std::to_string(index) + "]";
    if (const auto *proposition =
            std::get_if<PropositionInstance>(&hypothesis)) {
      RuntimeCheckResult propositionCheck = checkPropositionContext(
          context, *proposition, hypothesisLocation, state);
      if (!propositionCheck.accepted())
        return propositionCheck;
    } else {
      const auto &assumed =
          std::get<AssumedJudgmentHolds>(hypothesis).assertedJudgment;
      if (!assumed)
        return refuse(RuntimePhase::HypothesisValidation,
                      RuntimeRefusalCode::NullRecursiveValue,
                      hypothesisLocation,
                      "assumed-judgment hypothesis has a null judgment");
      if (!state.activeJudgments.insert(assumed.get()).second)
        return refuse(RuntimePhase::HypothesisValidation,
                      RuntimeRefusalCode::RecursiveCycle, hypothesisLocation,
                      "assumed-judgment graph contains a recursive cycle");
      RuntimeCheckResult assumedCheck = checkJudgmentImpl(
          context, *assumed, hypothesisLocation + ".asserted_judgment", state);
      state.activeJudgments.erase(assumed.get());
      if (!assumedCheck.accepted())
        return assumedCheck;
    }

    for (size_t previous = 0; previous < index; ++previous)
      if (hypothesisEqual(judgment.hypotheses[previous], hypothesis))
        return refuse(RuntimePhase::HypothesisValidation,
                      RuntimeRefusalCode::NonCanonicalNormalForm,
                      hypothesisLocation,
                      "hypothesis set contains an equal duplicate");
  }
  return accepted();
}

void appendGameSupport(const ClosedBound &bound,
                       std::vector<PrimitiveGameInstance> &support) {
  for (const PrimitiveGameTerm &term : bound.primitiveGameTerms) {
    if (std::find(support.begin(), support.end(), term.instance) ==
        support.end())
      support.push_back(term.instance);
  }
}

} // namespace

const char *runtimePhaseName(RuntimePhase phase) {
  switch (phase) {
  case RuntimePhase::ValueValidation:
    return "value_validation";
  case RuntimePhase::SubjectValidation:
    return "subject_validation";
  case RuntimePhase::QuantityValidation:
    return "quantity_validation";
  case RuntimePhase::BoundValidation:
    return "bound_validation";
  case RuntimePhase::ResultValidation:
    return "result_validation";
  case RuntimePhase::HypothesisValidation:
    return "hypothesis_validation";
  case RuntimePhase::JudgmentValidation:
    return "judgment_validation";
  case RuntimePhase::SiteResolution:
    return "site_resolution";
  case RuntimePhase::BindingResolution:
    return "binding_resolution";
  case RuntimePhase::PremiseResolution:
    return "premise_resolution";
  case RuntimePhase::ConditionEvaluation:
    return "condition_evaluation";
  case RuntimePhase::EqualitySolving:
    return "equality_solving";
  case RuntimePhase::ResourceSpecialization:
    return "resource_specialization";
  case RuntimePhase::RuleEvaluation:
    return "rule_evaluation";
  case RuntimePhase::Derivation:
    return "derivation";
  }
  return "unknown";
}

const char *runtimeRefusalCodeName(RuntimeRefusalCode code) {
  switch (code) {
  case RuntimeRefusalCode::InvalidReference:
    return "invalid_reference";
  case RuntimeRefusalCode::NullRecursiveValue:
    return "null_recursive_value";
  case RuntimeRefusalCode::RecursiveCycle:
    return "recursive_cycle";
  case RuntimeRefusalCode::SortMismatch:
    return "sort_mismatch";
  case RuntimeRefusalCode::InvalidPayload:
    return "invalid_payload";
  case RuntimeRefusalCode::EmptyCollection:
    return "empty_collection";
  case RuntimeRefusalCode::DuplicateName:
    return "duplicate_name";
  case RuntimeRefusalCode::NonCanonicalNormalForm:
    return "noncanonical_normal_form";
  case RuntimeRefusalCode::InvalidResource:
    return "invalid_resource";
  case RuntimeRefusalCode::UnknownSchema:
    return "unknown_schema";
  case RuntimeRefusalCode::UnknownIndex:
    return "unknown_index";
  case RuntimeRefusalCode::InvalidResultSchema:
    return "invalid_result_schema";
  case RuntimeRefusalCode::InvalidPrimitiveGame:
    return "invalid_primitive_game";
  case RuntimeRefusalCode::InvalidProposition:
    return "invalid_proposition";
  case RuntimeRefusalCode::SiteMismatch:
    return "site_mismatch";
  case RuntimeRefusalCode::BindingMismatch:
    return "binding_mismatch";
  case RuntimeRefusalCode::PremiseMismatch:
    return "premise_mismatch";
  case RuntimeRefusalCode::CoverageMismatch:
    return "coverage_mismatch";
  case RuntimeRefusalCode::ConditionFailed:
    return "condition_failed";
  case RuntimeRefusalCode::EqualityMismatch:
    return "equality_mismatch";
  case RuntimeRefusalCode::ArithmeticDomain:
    return "arithmetic_domain";
  case RuntimeRefusalCode::UnsupportedNormalForm:
    return "unsupported_normal_form";
  }
  return "unknown";
}

bool operator==(const ExactScalarValue &lhs, const ExactScalarValue &rhs) {
  if (lhs.sort != rhs.sort || lhs.payload.index() != rhs.payload.index())
    return false;
  if (const auto *number = std::get_if<registry::Rational>(&lhs.payload))
    return equalRational(*number, std::get<registry::Rational>(rhs.payload));
  if (const auto *text = std::get_if<std::string>(&lhs.payload))
    return *text == std::get<std::string>(rhs.payload);
  return std::get<bool>(lhs.payload) == std::get<bool>(rhs.payload);
}

bool operator!=(const ExactScalarValue &lhs, const ExactScalarValue &rhs) {
  return !(lhs == rhs);
}

bool operator==(const ReductionContractRoundValue &lhs,
                const ReductionContractRoundValue &rhs) {
  return equalRational(lhs.roundIndex, rhs.roundIndex) &&
         lhs.roundKind == rhs.roundKind &&
         lhs.challengeRole == rhs.challengeRole &&
         lhs.challengeEventPosition == rhs.challengeEventPosition &&
         lhs.challengePayloadClass == rhs.challengePayloadClass &&
         lhs.challengeDomain == rhs.challengeDomain &&
         equalRational(lhs.challengeSpace, rhs.challengeSpace) &&
         equalRational(lhs.challengeCount, rhs.challengeCount) &&
         lhs.challengeShape == rhs.challengeShape &&
         lhs.challengeSampling == rhs.challengeSampling &&
         lhs.messages == rhs.messages &&
         equalOptionalRational(lhs.roundDegree, rhs.roundDegree) &&
         equalOptionalRational(lhs.challengeSpaceLog2, rhs.challengeSpaceLog2);
}

bool operator!=(const ReductionContractRoundValue &lhs,
                const ReductionContractRoundValue &rhs) {
  return !(lhs == rhs);
}

bool operator==(const ReductionContractValue &lhs,
                const ReductionContractValue &rhs) {
  return lhs.ref == rhs.ref && lhs.inputCount == rhs.inputCount &&
         lhs.orderedInputAnchors == rhs.orderedInputAnchors &&
         lhs.orderedInputAnchorEventPositions ==
             rhs.orderedInputAnchorEventPositions &&
         lhs.parameters == rhs.parameters &&
         lhs.constrainedInputAnchors == rhs.constrainedInputAnchors &&
         lhs.committedArityByRole == rhs.committedArityByRole &&
         lhs.rounds == rhs.rounds;
}

bool operator!=(const ReductionContractValue &lhs,
                const ReductionContractValue &rhs) {
  return !(lhs == rhs);
}

bool operator==(const PathTransitionValue &lhs,
                const PathTransitionValue &rhs) {
  if (lhs.ref != rhs.ref || lhs.artifactId != rhs.artifactId ||
      lhs.claim != rhs.claim || bool(lhs.duplexFacts) != bool(rhs.duplexFacts))
    return false;
  return !lhs.duplexFacts || *lhs.duplexFacts == *rhs.duplexFacts;
}

bool operator!=(const PathTransitionValue &lhs,
                const PathTransitionValue &rhs) {
  return !(lhs == rhs);
}

bool operator==(const SrsInstanceValue &lhs, const SrsInstanceValue &rhs) {
  return lhs.ref == rhs.ref;
}

bool operator!=(const SrsInstanceValue &lhs, const SrsInstanceValue &rhs) {
  return !(lhs == rhs);
}

bool operator==(const FriDomainInstanceValue &lhs,
                const FriDomainInstanceValue &rhs) {
  return lhs.ref == rhs.ref;
}

bool operator!=(const FriDomainInstanceValue &lhs,
                const FriDomainInstanceValue &rhs) {
  return !(lhs == rhs);
}

RuntimeValue RuntimeValue::integer(registry::Rational value) {
  return RuntimeValue{ValueSort::Integer, std::move(value)};
}

RuntimeValue RuntimeValue::rational(registry::Rational value) {
  return RuntimeValue{ValueSort::Rational, std::move(value)};
}

RuntimeValue RuntimeValue::text(std::string value) {
  return RuntimeValue{ValueSort::String, std::move(value)};
}

RuntimeValue RuntimeValue::boolean(bool value) {
  return RuntimeValue{ValueSort::Boolean, value};
}

RuntimeValue RuntimeValue::subject(SecuritySubject value) {
  return RuntimeValue{
      ValueSort::Subject,
      std::make_shared<const SecuritySubject>(std::move(value))};
}

RuntimeValue RuntimeValue::reductionContract(ReductionContractValue value) {
  return RuntimeValue{ValueSort::ReductionContract, std::move(value)};
}

RuntimeValue RuntimeValue::pathTransition(PathTransitionValue value) {
  return RuntimeValue{ValueSort::PathTransition, std::move(value)};
}

RuntimeValue RuntimeValue::roundAdjacency(RoundAdjacencyValue value) {
  return RuntimeValue{ValueSort::RoundAdjacency, std::move(value)};
}

RuntimeValue RuntimeValue::algebra(AlgebraInstanceValue value) {
  return RuntimeValue{ValueSort::AlgebraInstance, std::move(value)};
}

RuntimeValue RuntimeValue::srs(SrsInstanceValue value) {
  return RuntimeValue{ValueSort::SrsInstance, std::move(value)};
}

RuntimeValue RuntimeValue::friDomain(FriDomainInstanceValue value) {
  return RuntimeValue{ValueSort::FriDomainInstance, std::move(value)};
}

bool operator==(const RuntimeValue &lhs, const RuntimeValue &rhs) {
  EqualityState state;
  return runtimeValueEqualImpl(lhs, rhs, state);
}

bool operator!=(const RuntimeValue &lhs, const RuntimeValue &rhs) {
  return !(lhs == rhs);
}

bool operator==(const ExternalInstanceSubject &lhs,
                const ExternalInstanceSubject &rhs) {
  EqualityState state;
  return externalSubjectEqualImpl(lhs, rhs, state);
}

bool operator!=(const ExternalInstanceSubject &lhs,
                const ExternalInstanceSubject &rhs) {
  return !(lhs == rhs);
}

bool operator==(const SecuritySubject &lhs, const SecuritySubject &rhs) {
  EqualityState state;
  return subjectEqualImpl(lhs, rhs, state);
}

bool operator!=(const SecuritySubject &lhs, const SecuritySubject &rhs) {
  return !(lhs == rhs);
}

bool operator==(const ResourceMonomial &lhs, const ResourceMonomial &rhs) {
  return equalRational(lhs.coefficient, rhs.coefficient) &&
         lhs.resource == rhs.resource && lhs.exponent == rhs.exponent;
}

bool operator!=(const ResourceMonomial &lhs, const ResourceMonomial &rhs) {
  return !(lhs == rhs);
}

bool operator==(const ClosedQuantity &lhs, const ClosedQuantity &rhs) {
  return equalRational(lhs.constant, rhs.constant) &&
         lhs.resourceTerms == rhs.resourceTerms;
}

bool operator!=(const ClosedQuantity &lhs, const ClosedQuantity &rhs) {
  return !(lhs == rhs);
}

bool operator==(const PrimitiveGameInstance &lhs,
                const PrimitiveGameInstance &rhs) {
  EqualityState state;
  return gameInstanceEqualImpl(lhs, rhs, state);
}

bool operator!=(const PrimitiveGameInstance &lhs,
                const PrimitiveGameInstance &rhs) {
  return !(lhs == rhs);
}

bool operator==(const PrimitiveGameTerm &lhs, const PrimitiveGameTerm &rhs) {
  EqualityState state;
  return primitiveTermEqualImpl(lhs, rhs, state);
}

bool operator!=(const PrimitiveGameTerm &lhs, const PrimitiveGameTerm &rhs) {
  return !(lhs == rhs);
}

bool operator==(const ClosedBound &lhs, const ClosedBound &rhs) {
  if (lhs.quantity != rhs.quantity ||
      lhs.primitiveGameTerms.size() != rhs.primitiveGameTerms.size())
    return false;
  std::vector<bool> used(rhs.primitiveGameTerms.size(), false);
  for (const PrimitiveGameTerm &left : lhs.primitiveGameTerms) {
    bool matched = false;
    for (size_t index = 0; index < rhs.primitiveGameTerms.size(); ++index) {
      if (!used[index] && left == rhs.primitiveGameTerms[index]) {
        used[index] = true;
        matched = true;
        break;
      }
    }
    if (!matched)
      return false;
  }
  return true;
}

bool operator!=(const ClosedBound &lhs, const ClosedBound &rhs) {
  return !(lhs == rhs);
}

bool operator==(const ExtractionCoordinate &lhs,
                const ExtractionCoordinate &rhs) {
  return lhs.label == rhs.label && lhs.arity == rhs.arity &&
         lhs.challengeSpace == rhs.challengeSpace;
}

bool operator!=(const ExtractionCoordinate &lhs,
                const ExtractionCoordinate &rhs) {
  return !(lhs == rhs);
}

bool operator==(const ExtractionResult &lhs, const ExtractionResult &rhs) {
  return lhs.coordinates == rhs.coordinates &&
         lhs.failureBound == rhs.failureBound;
}

bool operator!=(const ExtractionResult &lhs, const ExtractionResult &rhs) {
  return !(lhs == rhs);
}

bool operator==(const RoundStatePredicate &lhs,
                const RoundStatePredicate &rhs) {
  return lhs.claimUnsatisfied == rhs.claimUnsatisfied;
}

bool operator!=(const RoundStatePredicate &lhs,
                const RoundStatePredicate &rhs) {
  return !(lhs == rhs);
}

bool operator==(const RoundResultEntry &lhs, const RoundResultEntry &rhs) {
  return lhs.roundIndex == rhs.roundIndex &&
         lhs.challengeSpace == rhs.challengeSpace && lhs.bound == rhs.bound &&
         lhs.statePredicate == rhs.statePredicate;
}

bool operator!=(const RoundResultEntry &lhs, const RoundResultEntry &rhs) {
  return !(lhs == rhs);
}

bool operator==(const RoundResult &lhs, const RoundResult &rhs) {
  return lhs.rounds == rhs.rounds;
}

bool operator!=(const RoundResult &lhs, const RoundResult &rhs) {
  return !(lhs == rhs);
}

bool operator==(const ScalarResult &lhs, const ScalarResult &rhs) {
  return lhs.bound == rhs.bound;
}

bool operator!=(const ScalarResult &lhs, const ScalarResult &rhs) {
  return !(lhs == rhs);
}

bool securityResultEqual(const SecurityResult &lhs, const SecurityResult &rhs) {
  if (lhs.index() != rhs.index())
    return false;
  if (const auto *extraction = std::get_if<ExtractionResult>(&lhs))
    return *extraction == std::get<ExtractionResult>(rhs);
  if (const auto *rounds = std::get_if<RoundResult>(&lhs))
    return *rounds == std::get<RoundResult>(rhs);
  return std::get<ScalarResult>(lhs) == std::get<ScalarResult>(rhs);
}

ResultSchema resultSchemaOf(const SecurityResult &result) {
  if (std::holds_alternative<ExtractionResult>(result))
    return ResultSchema::Extraction;
  if (std::holds_alternative<RoundResult>(result))
    return ResultSchema::Round;
  return ResultSchema::Scalar;
}

bool operator==(const PropositionInstance &lhs,
                const PropositionInstance &rhs) {
  EqualityState state;
  return propositionEqualImpl(lhs, rhs, state);
}

bool operator!=(const PropositionInstance &lhs,
                const PropositionInstance &rhs) {
  return !(lhs == rhs);
}

bool hypothesisEqual(const Hypothesis &lhs, const Hypothesis &rhs) {
  EqualityState state;
  return hypothesisEqualImpl(lhs, rhs, state);
}

bool operator==(const SecurityJudgment &lhs, const SecurityJudgment &rhs) {
  EqualityState state;
  return judgmentEqualImpl(lhs, rhs, state);
}

bool operator!=(const SecurityJudgment &lhs, const SecurityJudgment &rhs) {
  return !(lhs == rhs);
}

RuntimeCheckResult checkRuntimeValueWellFormed(const RuntimeValue &value,
                                               std::string location) {
  CheckState state;
  return checkRuntimeValueImpl(value, location, state);
}

RuntimeCheckResult
checkSecuritySubjectWellFormed(const SecuritySubject &subject,
                               std::string location) {
  CheckState state;
  state.activeSubjects.insert(&subject);
  RuntimeCheckResult result = checkSubjectImpl(subject, location, state);
  state.activeSubjects.erase(&subject);
  return result;
}

RuntimeCheckResult checkClosedQuantityWellFormed(const ClosedQuantity &quantity,
                                                 std::string location) {
  return checkQuantityImpl(quantity, location);
}

RuntimeCheckResult checkClosedBoundWellFormed(const ClosedBound &bound,
                                              std::string location) {
  CheckState state;
  return checkBoundImpl(bound, location, state);
}

RuntimeCheckResult
checkSecurityJudgmentWellFormed(const SchemaContext &context,
                                const SecurityJudgment &judgment,
                                std::string location) {
  CheckState state;
  state.activeJudgments.insert(&judgment);
  RuntimeCheckResult result =
      checkJudgmentImpl(context, judgment, location, state);
  state.activeJudgments.erase(&judgment);
  return result;
}

std::vector<PrimitiveGameInstance> gameSupport(const SecurityResult &result) {
  std::vector<PrimitiveGameInstance> support;
  if (const auto *extraction = std::get_if<ExtractionResult>(&result)) {
    if (extraction->failureBound)
      appendGameSupport(*extraction->failureBound, support);
  } else if (const auto *rounds = std::get_if<RoundResult>(&result)) {
    for (const RoundResultEntry &round : rounds->rounds)
      appendGameSupport(round.bound, support);
  } else {
    appendGameSupport(std::get<ScalarResult>(result).bound, support);
  }
  return support;
}

} // namespace zkc::soundness
