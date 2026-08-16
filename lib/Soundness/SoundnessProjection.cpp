//===- SoundnessProjection.cpp - Closed fact projection/deciders ---------===//
#include "zkc/Soundness/SoundnessProjection.h"

#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/Twine.h"

#include <algorithm>
#include <cstdint>
#include <limits>
#include <optional>
#include <string>
#include <utility>

namespace zkc::soundness {
namespace {

constexpr int64_t kMaxExactExponent = 4096;

llvm::Error projectionError(const llvm::Twine &detail) {
  return llvm::createStringError("soundness projection: " + detail);
}

llvm::Error deciderError(const llvm::Twine &detail) {
  return llvm::createStringError("soundness machine decider: " + detail);
}

bool validRef(const ExactRef &ref) {
  return !ref.id.empty() && !ref.sourceRevision.empty();
}

bool equalRational(const registry::Rational &left,
                   const registry::Rational &right) {
  return left.compare(right) == 0;
}

bool isInteger(const registry::Rational &value) {
  return value.denStr() == "1";
}

bool isPositiveInteger(const registry::Rational &value) {
  return isInteger(value) &&
         value.compare(registry::Rational::fromInteger(0)) > 0;
}

llvm::Expected<registry::Rational> rationalFromUint64(uint64_t value) {
  return registry::Rational::fromDecimal(std::to_string(value));
}

llvm::Error malformedRuntimeValue(const RuntimeCheckResult &check,
                                  const llvm::Twine &location) {
  if (!check.refusal)
    return deciderError(location + " is malformed");
  return deciderError(location + " is malformed at " + check.refusal->location +
                      " (" + runtimeRefusalCodeName(check.refusal->code) +
                      "): " + check.refusal->detail);
}

llvm::Expected<const SealedReduction *>
reductionAt(const SealedSoundnessView &sealed, const ApplicationSite &site) {
  const auto *occurrence = std::get_if<ReductionOccurrence>(&site);
  if (!occurrence)
    return projectionError(
        "a reduction-relative projection was used at a path occurrence");

  auto owner = resolveReductionOutput(sealed, *occurrence);
  if (!owner)
    return owner.takeError();
  (void)owner;

  auto found = sealed.reductionsByTransformerPosition.find(
      occurrence->transformerPosition);
  if (found == sealed.reductionsByTransformerPosition.end() ||
      found->second.transformerPosition != occurrence->transformerPosition)
    return projectionError(
        "the validated reduction occurrence has no exact owned reduction");
  return &found->second;
}

llvm::Expected<const SealedDuplexFacts *>
duplexAt(const SealedSoundnessView &sealed, const ApplicationSite &site) {
  if (!std::holds_alternative<PathOccurrence>(site))
    return projectionError(
        "a path-relative projection was used at a reduction occurrence");
  auto subject = subjectOf(sealed, site);
  if (!subject)
    return subject.takeError();
  (void)subject;
  if (!sealed.duplex)
    return projectionError(
        "the authenticated path has no sealed duplex construction facts");
  return &*sealed.duplex;
}

llvm::Expected<ExactScalarValue>
copyParameterAtom(const SealedParameterAtom &atom) {
  ExactScalarValue result;
  switch (atom.carrier) {
  case SealedParameterAtom::Carrier::String: {
    const auto *value = std::get_if<std::string>(&atom.value);
    if (!value)
      return projectionError("string parameter atom has the wrong carrier");
    result.sort = ValueSort::String;
    result.payload = *value;
    return result;
  }
  case SealedParameterAtom::Carrier::Integer: {
    const auto *value = std::get_if<registry::Rational>(&atom.value);
    if (!value || !isInteger(*value))
      return projectionError("integer parameter atom is not an exact integer");
    result.sort = ValueSort::Integer;
    result.payload = *value;
    return result;
  }
  case SealedParameterAtom::Carrier::Boolean: {
    const auto *value = std::get_if<bool>(&atom.value);
    if (!value)
      return projectionError("Boolean parameter atom has the wrong carrier");
    result.sort = ValueSort::Boolean;
    result.payload = *value;
    return result;
  }
  }
  return projectionError("parameter atom has an unknown carrier");
}

llvm::Expected<ReductionContractValue>
makeReductionContract(const SealedReduction &sealed) {
  ReductionContractValue result;
  result.ref = sealed.contractRef;
  result.inputCount = sealed.orderedInputs.size();
  result.orderedInputAnchors = sealed.orderedInputAnchors;
  result.orderedInputAnchorEventPositions =
      sealed.orderedInputAnchorEventPositions;

  for (const auto &[name, atom] : sealed.parameters) {
    auto copied = copyParameterAtom(atom);
    if (!copied)
      return copied.takeError();
    result.parameters.emplace(name, std::move(*copied));
  }

  result.rounds.reserve(sealed.rounds.size());
  for (const SealedRoundFact &round : sealed.rounds) {
    auto roundIndex = rationalFromUint64(round.position);
    if (!roundIndex)
      return roundIndex.takeError();
    auto challengeCount = rationalFromUint64(round.challengeCount);
    if (!challengeCount)
      return challengeCount.takeError();

    ReductionContractRoundValue copied;
    copied.roundIndex = std::move(*roundIndex);
    copied.roundKind = round.kind;
    copied.challengeRole = round.challengeRole;
    copied.challengeEventPosition = round.challengeEventPosition;
    copied.challengePayloadClass = round.challengePayloadClass;
    copied.challengeDomain = round.challengeDomain;
    copied.challengeSpace = round.challengeSpace;
    copied.challengeCount = std::move(*challengeCount);
    copied.challengeShape = round.shape;
    copied.challengeSampling = round.sampling;
    copied.messages = round.messages;
    copied.roundDegree = round.roundDegree;
    copied.challengeSpaceLog2 = round.challengeSpaceLog2;
    result.rounds.push_back(std::move(copied));
  }

  RuntimeValue wrapped = RuntimeValue::reductionContract(result);
  RuntimeCheckResult check =
      checkRuntimeValueWellFormed(wrapped, "projected_reduction_contract");
  if (!check.accepted())
    return malformedRuntimeValue(check, "authenticated reduction contract");
  return result;
}

llvm::Expected<registry::Rational>
parseParameterNumber(const SealedParameterAtom &atom, ValueSort resultSort) {
  registry::Rational value;
  if (atom.carrier == SealedParameterAtom::Carrier::Integer) {
    const auto *number = std::get_if<registry::Rational>(&atom.value);
    if (!number)
      return projectionError("integer parameter atom has the wrong carrier");
    value = *number;
  } else if (atom.carrier == SealedParameterAtom::Carrier::String) {
    const auto *text = std::get_if<std::string>(&atom.value);
    if (!text)
      return projectionError("string parameter atom has the wrong carrier");
    size_t slash = text->find('/');
    if (slash == std::string::npos) {
      auto parsed = registry::Rational::fromDecimal(*text);
      if (!parsed)
        return parsed.takeError();
      value = std::move(*parsed);
    } else {
      auto parsed = registry::Rational::fromDecimalPair(
          llvm::StringRef(*text).take_front(slash),
          llvm::StringRef(*text).drop_front(slash + 1));
      if (!parsed)
        return parsed.takeError();
      value = std::move(*parsed);
    }
  } else {
    return projectionError(
        "a numeric reduction parameter has a nonnumeric carrier");
  }

  if (resultSort == ValueSort::Integer && !isInteger(value))
    return projectionError(
        "an integer reduction-parameter projection resolved a fraction");
  return value;
}

llvm::Expected<RuntimeValue>
projectReductionParameter(const SealedReduction &sealed,
                          const ArtifactProjection &projection) {
  auto found = sealed.parameters.find(projection.field);
  if (found == sealed.parameters.end())
    return projectionError("reduction parameter '" + projection.field +
                           "' is absent");

  switch (projection.resultSort) {
  case ValueSort::Integer:
  case ValueSort::Rational: {
    auto number = parseParameterNumber(found->second, projection.resultSort);
    if (!number)
      return number.takeError();
    return projection.resultSort == ValueSort::Integer
               ? RuntimeValue::integer(std::move(*number))
               : RuntimeValue::rational(std::move(*number));
  }
  case ValueSort::String: {
    if (found->second.carrier != SealedParameterAtom::Carrier::String)
      return projectionError(
          "a string reduction-parameter projection has a non-string carrier");
    const auto *value = std::get_if<std::string>(&found->second.value);
    if (!value)
      return projectionError("string parameter atom has the wrong carrier");
    return RuntimeValue::text(*value);
  }
  case ValueSort::Boolean: {
    if (found->second.carrier != SealedParameterAtom::Carrier::Boolean)
      return projectionError(
          "a Boolean reduction-parameter projection has a non-Boolean "
          "carrier");
    const auto *value = std::get_if<bool>(&found->second.value);
    if (!value)
      return projectionError("Boolean parameter atom has the wrong carrier");
    return RuntimeValue::boolean(*value);
  }
  default:
    return projectionError(
        "a reduction-parameter projection requested a nonscalar sort");
  }
}

bool roundSelected(const ReductionContractRoundValue &round,
                   const ContractRoundSelector &selector) {
  switch (selector.kind) {
  case ContractRoundSelectorKind::AllContractRounds:
    return true;
  case ContractRoundSelectorKind::RoundKind:
    return round.roundKind == selector.roundKind;
  case ContractRoundSelectorKind::RoundPosition: {
    auto position = rationalFromUint64(selector.position);
    return position && equalRational(round.roundIndex, *position);
  }
  }
  return false;
}

llvm::Expected<RuntimeValue>
roundField(const ReductionContractRoundValue &round,
           const ArtifactProjection &projection) {
  if (projection.field == "RoundIndex")
    return RuntimeValue::integer(round.roundIndex);
  if (projection.field == "RoundKind")
    return RuntimeValue::text(round.roundKind);
  if (projection.field == "ChallengeSpace")
    return RuntimeValue::integer(round.challengeSpace);
  if (projection.field == "ChallengeCount") {
    // ChallengeCount means a theorem-level IID repetition count.  A scalar's
    // implicit count one is not such a witness, and correlated vectors are
    // outside the admitted loss formulas.
    if (round.challengeShape != ChallengeShape::Vector ||
        round.challengeSampling != ChallengeSampling::UniformIndependent)
      return projectionError(
          "ChallengeCount requires an IID vector challenge; scalar or "
          "non-IID sampling refuses");
    return RuntimeValue::integer(round.challengeCount);
  }
  if (projection.field == "RoundDegree") {
    if (!round.roundDegree)
      return projectionError(
          "selected contract round has no exact round degree");
    return RuntimeValue::integer(*round.roundDegree);
  }
  if (projection.field == "ChallengeSpaceLog2") {
    if (!round.challengeSpaceLog2)
      return projectionError(
          "selected contract round has no exact challenge-space log2");
    return RuntimeValue::integer(*round.challengeSpaceLog2);
  }
  return projectionError("unknown contract-round field '" + projection.field +
                         "'");
}

llvm::Expected<RuntimeValue>
projectRoundFamily(const ReductionContractValue &contract,
                   const ArtifactProjection &projection) {
  std::vector<const ReductionContractRoundValue *> selected;
  for (const ReductionContractRoundValue &round : contract.rounds)
    if (roundSelected(round, projection.roundSelector))
      selected.push_back(&round);
  if (selected.empty())
    return projectionError("contract-round selector matched no round");

  if (projection.aggregate == ProjectionAggregate::Count) {
    if (projection.resultSort != ValueSort::Integer)
      return projectionError("round-family Count requested a noninteger sort");
    auto count = rationalFromUint64(selected.size());
    if (!count)
      return count.takeError();
    return RuntimeValue::integer(std::move(*count));
  }
  if (projection.aggregate != ProjectionAggregate::UniqueEqual)
    return projectionError("unknown contract-round projection aggregate");

  auto first = roundField(*selected.front(), projection);
  if (!first)
    return first.takeError();
  if (first->sort != projection.resultSort)
    return projectionError(
        "contract-round field resolved with a different result sort");
  for (size_t index = 1; index < selected.size(); ++index) {
    auto current = roundField(*selected[index], projection);
    if (!current)
      return current.takeError();
    if (*current != *first)
      return projectionError(
          "UniqueEqual contract-round projection selected unequal values");
  }
  return std::move(*first);
}

llvm::Expected<llvm::APInt>
apFromPositiveInteger(const registry::Rational &value,
                      const llvm::Twine &location) {
  if (!isPositiveInteger(value))
    return projectionError(location + " is not a positive integer");
  std::string text = value.numStr();
  unsigned bits = llvm::APInt::getBitsNeeded(text, 10);
  return llvm::APInt(std::max(bits, 1u), text, 10);
}

llvm::Expected<registry::Rational>
rationalFromFraction(const llvm::APInt &numerator,
                     const llvm::APInt &denominator) {
  llvm::SmallString<64> numeratorText;
  llvm::SmallString<64> denominatorText;
  numerator.toString(numeratorText, 10, /*Signed=*/false);
  denominator.toString(denominatorText, 10, /*Signed=*/false);
  return registry::Rational::fromDecimalPair(numeratorText, denominatorText);
}

struct ComputedCodecBiases {
  registry::Rational max;
  registry::Rational sum;
};

llvm::Expected<ComputedCodecBiases>
computeCodecBiases(const SealedDuplexFacts &facts) {
  if (!validRef(facts.spongeRef))
    return projectionError("duplex sponge has no exact reference");
  auto alphabet =
      apFromPositiveInteger(facts.alphabetOrder, "duplex alphabet order");
  if (!alphabet)
    return alphabet.takeError();
  if (facts.capacity == 0 || facts.rate == 0)
    return projectionError("duplex capacity and rate must be positive");
  if (facts.challenges.empty())
    return projectionError(
        "duplex construction carries no complete challenge-codec facts");

  ComputedCodecBiases result;
  std::optional<uint64_t> previousEvent;
  constexpr uint64_t maxDomainBits = uint64_t(1) << 20;
  for (const SealedChallengeCodecFact &challenge : facts.challenges) {
    if (previousEvent && challenge.eventPosition <= *previousEvent)
      return projectionError(
          "duplex challenge-codec facts are not in strict event order");
    previousEvent = challenge.eventPosition;
    if (challenge.payloadClass.empty() || challenge.domain.empty() ||
        !validRef(challenge.codecRef) || challenge.squeezeSymbols == 0)
      return projectionError(
          "duplex challenge has incomplete semantic codec facts");
    if ((challenge.shape == ChallengeShape::Scalar &&
         (challenge.count != 1 ||
          challenge.sampling != ChallengeSampling::Uniform)) ||
        (challenge.shape == ChallengeShape::Vector &&
         (challenge.count < 2 ||
          challenge.sampling != ChallengeSampling::UniformIndependent)))
      return projectionError(
          "duplex challenge shape, count, and sampling disagree");

    auto space =
        apFromPositiveInteger(challenge.space, "duplex challenge space");
    if (!space)
      return space.takeError();

    uint64_t alphabetBits = alphabet->getBitWidth();
    if (alphabetBits == 0 ||
        challenge.squeezeSymbols >
            (maxDomainBits - 1) / std::max<uint64_t>(alphabetBits, 1))
      return projectionError(
          "duplex squeeze domain exceeds the exact computation limit");
    uint64_t widthNeeded =
        alphabetBits * challenge.squeezeSymbols + uint64_t(1);
    if (widthNeeded > maxDomainBits ||
        widthNeeded > std::numeric_limits<unsigned>::max())
      return projectionError(
          "duplex squeeze domain exceeds the exact computation limit");

    unsigned width = static_cast<unsigned>(widthNeeded);
    llvm::APInt domain(width, 1);
    llvm::APInt base = alphabet->zext(width);
    for (uint64_t symbol = 0; symbol < challenge.squeezeSymbols; ++symbol)
      domain *= base;

    unsigned common = std::max(domain.getBitWidth(), space->getBitWidth());
    llvm::APInt n = domain.zext(common);
    llvm::APInt q = space->zext(common);
    registry::Rational perDraw;
    switch (challenge.codecKind) {
    case CodecKind::TupleBijection:
      if (q != n)
        return projectionError(
            "tuple-bijection codec target is not its exact squeeze domain");
      break;
    case CodecKind::ModReduce:
      if (q.ugt(n))
        return projectionError(
            "mod-reduce challenge space exceeds its squeeze domain");
      if (llvm::APInt residue = n.urem(q); !residue.isZero()) {
        unsigned wide = common * 2;
        llvm::APInt numerator = residue.zext(wide) * (q - residue).zext(wide);
        llvm::APInt denominator = n.zext(wide) * q.zext(wide);
        auto exact = rationalFromFraction(numerator, denominator);
        if (!exact)
          return exact.takeError();
        perDraw = std::move(*exact);
      }
      break;
    }

    auto count = rationalFromUint64(challenge.count);
    if (!count)
      return count.takeError();
    registry::Rational eventBias = perDraw.mul(*count);
    if (!equalRational(eventBias, challenge.biasContribution))
      return projectionError(
          "stored challenge codec-bias contribution is not the exact "
          "recomputed value");
    if (result.max.compare(eventBias) < 0)
      result.max = eventBias;
    result.sum = result.sum.add(eventBias);
  }

  if (!equalRational(result.max, facts.codecBiasMax) ||
      !equalRational(result.sum, facts.codecBiasSum))
    return projectionError(
        "stored duplex codec-bias aggregate is not the exact recomputed "
        "aggregate");
  return result;
}

llvm::Expected<RuntimeValue>
projectPathField(const SealedSoundnessView &sealed, const ApplicationSite &site,
                 const ArtifactProjection &projection) {
  auto facts = duplexAt(sealed, site);
  if (!facts)
    return facts.takeError();

  if (projection.field == "sponge.alphabet_order") {
    if (projection.resultSort != ValueSort::Integer)
      return projectionError("sponge alphabet order has noninteger sort");
    return RuntimeValue::integer((*facts)->alphabetOrder);
  }
  if (projection.field == "sponge.capacity") {
    if (projection.resultSort != ValueSort::Integer)
      return projectionError("sponge capacity has noninteger sort");
    auto value = rationalFromUint64((*facts)->capacity);
    if (!value)
      return value.takeError();
    return RuntimeValue::integer(std::move(*value));
  }
  if (projection.field == "sponge.rate") {
    if (projection.resultSort != ValueSort::Integer)
      return projectionError("sponge rate has noninteger sort");
    auto value = rationalFromUint64((*facts)->rate);
    if (!value)
      return value.takeError();
    return RuntimeValue::integer(std::move(*value));
  }
  if (projection.field == "codec_bias_max" ||
      projection.field == "codec_bias_sum") {
    if (projection.resultSort != ValueSort::Rational)
      return projectionError("codec-bias projection has nonrational sort");
    auto computed = computeCodecBiases(**facts);
    if (!computed)
      return computed.takeError();
    return RuntimeValue::rational(
        projection.field == "codec_bias_max" ? computed->max : computed->sum);
  }
  return projectionError("unknown path-binding field '" + projection.field +
                         "'");
}

std::vector<ValueSort> argumentSorts(MachineDeciderKind kind) {
  switch (kind) {
  case MachineDeciderKind::OneMessageRole:
  case MachineDeciderKind::BoundBites:
  case MachineDeciderKind::SamePoint:
  case MachineDeciderKind::BatchAfterMaterial:
    return {ValueSort::ReductionContract};
  case MachineDeciderKind::SpaceEmbeds:
  case MachineDeciderKind::SpaceCoversArity:
    return {ValueSort::ReductionContract, ValueSort::Integer};
  case MachineDeciderKind::FieldClass:
    return {ValueSort::ReductionContract, ValueSort::String};
  case MachineDeciderKind::BatchArity:
  case MachineDeciderKind::JohnsonFoldParam:
    return {ValueSort::Integer};
  case MachineDeciderKind::SpaceCoversBatch:
    return {ValueSort::Integer, ValueSort::Integer};
  case MachineDeciderKind::UdrDomainFloor:
    return {ValueSort::Integer, ValueSort::Integer, ValueSort::Integer};
  case MachineDeciderKind::FriShape:
    return {ValueSort::Integer, ValueSort::Integer, ValueSort::Integer,
            ValueSort::Integer};
  case MachineDeciderKind::JohnsonSlack:
    return {ValueSort::Rational, ValueSort::Integer, ValueSort::Integer};
  case MachineDeciderKind::JohnsonMultiplicity:
    return {ValueSort::Integer, ValueSort::Rational, ValueSort::Integer};
  case MachineDeciderKind::JohnsonDelta:
    return {ValueSort::Rational, ValueSort::Rational, ValueSort::Integer};
  case MachineDeciderKind::UdrThetaWindow:
    return {ValueSort::Rational, ValueSort::Integer, ValueSort::Integer};
  case MachineDeciderKind::ThresholdDeltaWindow:
    return {ValueSort::Rational, ValueSort::Integer};
  case MachineDeciderKind::RandomWordsEtaFloor:
    return {ValueSort::Rational, ValueSort::Integer, ValueSort::Integer};
  case MachineDeciderKind::PowPinned:
  case MachineDeciderKind::PowAdjacent:
    return {ValueSort::RoundAdjacency};
  case MachineDeciderKind::DuplexSpine:
  case MachineDeciderKind::CodecBiasDeclared:
    return {ValueSort::PathTransition};
  }
  return {};
}

llvm::Error checkDeciderArguments(MachineDeciderKind kind,
                                  const std::vector<RuntimeValue> &arguments) {
  std::vector<ValueSort> expected = argumentSorts(kind);
  if (arguments.size() != expected.size())
    return deciderError("argument arity does not match the closed predicate");
  for (size_t index = 0; index < arguments.size(); ++index) {
    if (arguments[index].sort != expected[index])
      return deciderError("argument " + llvm::Twine(index) +
                          " has the wrong value sort");
    RuntimeCheckResult check = checkRuntimeValueWellFormed(
        arguments[index], "machine_argument[" + std::to_string(index) + "]");
    if (!check.accepted())
      return malformedRuntimeValue(check,
                                   "machine argument " + llvm::Twine(index));
  }
  return llvm::Error::success();
}

const registry::Rational &number(const RuntimeValue &value) {
  return std::get<registry::Rational>(value.payload);
}

const ReductionContractValue &contract(const RuntimeValue &value) {
  return std::get<ReductionContractValue>(value.payload);
}

const RoundAdjacencyValue &adjacency(const RuntimeValue &value) {
  return std::get<RoundAdjacencyValue>(value.payload);
}

const PathTransitionValue &path(const RuntimeValue &value) {
  return std::get<PathTransitionValue>(value.payload);
}

const std::string &text(const RuntimeValue &value) {
  return std::get<std::string>(value.payload);
}

llvm::Expected<registry::Rational> sqrtRhoBound(const registry::Rational &blowup,
                                                bool upper) {
  auto half = blowup.div(registry::Rational::fromInteger(2));
  if (!half)
    return half.takeError();
  auto exponent = upper ? half->floorToInt() : half->ceilToInt();
  if (!exponent)
    return exponent.takeError();
  if (*exponent < -kMaxExactExponent || *exponent > kMaxExactExponent)
    return deciderError(
        "dyadic exponent exceeds the v0 exact arithmetic range");
  return registry::Rational::fromInteger(2).pow(-*exponent);
}

llvm::Expected<std::pair<registry::Rational, registry::Rational>>
udrLastRound(const registry::Rational &n, const registry::Rational &k) {
  auto exponent = n.sub(k).add(registry::Rational::fromInteger(1)).floorToInt();
  if (!exponent)
    return exponent.takeError();
  if (*exponent < -kMaxExactExponent || *exponent > kMaxExactExponent)
    return deciderError(
        "dyadic exponent exceeds the v0 exact arithmetic range");
  auto blockLength = registry::Rational::fromInteger(2).pow(*exponent);
  if (!blockLength)
    return blockLength.takeError();
  auto rate = registry::Rational::fromInteger(2).pow(-*exponent);
  if (!rate)
    return rate.takeError();
  return std::make_pair(registry::Rational::fromInteger(1).sub(*rate),
                        std::move(*blockLength));
}

bool positive(const registry::Rational &value) {
  return value.compare(registry::Rational::fromInteger(0)) > 0;
}

} // namespace

llvm::Expected<RuntimeValue>
projectArtifactFact(const SealedSoundnessView &sealed,
                    const ApplicationSite &site,
                    const ArtifactProjection &projection) {
  if (projection.kind == ArtifactProjectionKind::PathBindingField)
    return projectPathField(sealed, site, projection);

  auto reduction = reductionAt(sealed, site);
  if (!reduction)
    return reduction.takeError();

  switch (projection.kind) {
  case ArtifactProjectionKind::ConclusionReductionContract: {
    if (projection.resultSort != ValueSort::ReductionContract)
      return projectionError(
          "conclusion-contract projection has the wrong result sort");
    auto copied = makeReductionContract(**reduction);
    if (!copied)
      return copied.takeError();
    return RuntimeValue::reductionContract(std::move(*copied));
  }
  case ArtifactProjectionKind::ContractRoundAdjacency:
    if (projection.resultSort != ValueSort::RoundAdjacency)
      return projectionError(
          "round-adjacency projection has the wrong result sort");
    if (!(*reduction)->roundAdjacency)
      return projectionError(
          "reduction occurrence has no authenticated round adjacency");
    return RuntimeValue::roundAdjacency(*(*reduction)->roundAdjacency);
  case ArtifactProjectionKind::ReductionInputCount: {
    if (projection.resultSort != ValueSort::Integer)
      return projectionError(
          "reduction-input-count projection has the wrong result sort");
    auto count = rationalFromUint64((*reduction)->orderedInputs.size());
    if (!count)
      return count.takeError();
    return RuntimeValue::integer(std::move(*count));
  }
  case ArtifactProjectionKind::ReductionParameter:
    return projectReductionParameter(**reduction, projection);
  case ArtifactProjectionKind::ContractRoundFamilyField: {
    auto copied = makeReductionContract(**reduction);
    if (!copied)
      return copied.takeError();
    return projectRoundFamily(*copied, projection);
  }
  case ArtifactProjectionKind::PathBindingField:
    break;
  }
  return projectionError("unknown artifact projection kind");
}

llvm::Expected<RuntimeValue>
resolveApplicationPathTransition(const SealedSoundnessView &sealed,
                                 const ApplicationSite &site,
                                 const RuleBinding &authorizedBinding) {
  const auto *occurrence = std::get_if<PathOccurrence>(&site);
  if (!occurrence)
    return projectionError(
        "ApplicationPathTransition was used at a reduction occurrence");
  auto subject = subjectOf(sealed, site);
  if (!subject)
    return subject.takeError();
  (void)subject;

  if (!validRef(authorizedBinding.ref))
    return projectionError("selected path binding reference is not exact");
  if (authorizedBinding.anchor.kind != ProtocolAnchorKind::PathTransition ||
      !validRef(authorizedBinding.anchor.ref))
    return projectionError(
        "authorized binding has no exact PathTransition anchor");

  PathTransitionValue transition;
  transition.ref = authorizedBinding.anchor.ref;
  transition.artifactId = sealed.artifactId;
  transition.claim = occurrence->claim;
  if (sealed.duplex)
    transition.duplexFacts =
        std::make_shared<const SealedDuplexFacts>(*sealed.duplex);
  RuntimeValue result = RuntimeValue::pathTransition(std::move(transition));
  RuntimeCheckResult check =
      checkRuntimeValueWellFormed(result, "application_path_transition");
  if (!check.accepted())
    return malformedRuntimeValue(check, "application path transition");
  return result;
}

llvm::Expected<bool>
evaluateMachineDecider(MachineDeciderKind kind,
                       const std::vector<RuntimeValue> &arguments) {
  if (llvm::Error error = checkDeciderArguments(kind, arguments))
    return std::move(error);

  const registry::Rational one = registry::Rational::fromInteger(1);
  switch (kind) {
  case MachineDeciderKind::OneMessageRole: {
    for (const ReductionContractRoundValue &round :
         contract(arguments[0]).rounds) {
      if (round.messages.size() != 1 ||
          round.messages.front().payloadClassesByOccurrence.size() < 2 ||
          !round.roundDegree)
        return false;
      auto occurrences = rationalFromUint64(
          round.messages.front().payloadClassesByOccurrence.size() - 1);
      if (!occurrences)
        return occurrences.takeError();
      if (!equalRational(*occurrences, *round.roundDegree))
        return false;
    }
    return true;
  }
  case MachineDeciderKind::SpaceEmbeds: {
    const registry::Rational &fieldOrder = number(arguments[1]);
    if (!positive(fieldOrder))
      return false;
    return llvm::all_of(contract(arguments[0]).rounds,
                        [&](const ReductionContractRoundValue &round) {
                          return round.challengeSpace.compare(fieldOrder) <= 0;
                        });
  }
  case MachineDeciderKind::BoundBites:
    return llvm::all_of(
        contract(arguments[0]).rounds,
        [&](const ReductionContractRoundValue &round) {
          return round.roundDegree && positive(*round.roundDegree) &&
                 round.roundDegree->compare(round.challengeSpace) < 0;
        });
  case MachineDeciderKind::FieldClass: {
    const std::string &fieldClass = text(arguments[1]);
    if (fieldClass.empty())
      return false;
    bool sawMessage = false;
    for (const ReductionContractRoundValue &round :
         contract(arguments[0]).rounds)
      for (const SealedMessageRoleFact &message : round.messages) {
        sawMessage = true;
        if (!llvm::all_of(message.payloadClassesByOccurrence,
                          [&](const std::string &payloadClass) {
                            return payloadClass == fieldClass;
                          }))
          return false;
      }
    return sawMessage;
  }
  case MachineDeciderKind::SpaceCoversArity: {
    const registry::Rational &arity = number(arguments[1]);
    if (!positive(arity))
      return false;
    return llvm::all_of(contract(arguments[0]).rounds,
                        [&](const ReductionContractRoundValue &round) {
                          return round.challengeSpace.compare(arity) >= 0;
                        });
  }
  case MachineDeciderKind::BatchArity:
    return number(arguments[0]).compare(registry::Rational::fromInteger(2)) >=
           0;
  case MachineDeciderKind::SpaceCoversBatch:
    return positive(number(arguments[1])) &&
           number(arguments[0]).compare(number(arguments[1])) >= 0;
  case MachineDeciderKind::SamePoint: {
    const ReductionContractValue &value = contract(arguments[0]);
    if (value.orderedInputAnchors.size() != value.inputCount ||
        value.inputCount < 2)
      return false;
    std::optional<std::string> point;
    for (const auto &anchors : value.orderedInputAnchors) {
      auto found = anchors.find("point");
      if (found == anchors.end() || found->second.empty())
        return false;
      if (!point)
        point = found->second;
      else if (*point != found->second)
        return false;
    }
    return true;
  }
  case MachineDeciderKind::BatchAfterMaterial: {
    const ReductionContractValue &value = contract(arguments[0]);
    if (value.orderedInputAnchors.size() != value.inputCount ||
        value.orderedInputAnchorEventPositions.size() != value.inputCount ||
        value.inputCount < 2 || value.rounds.size() != 1)
      return false;
    uint64_t challengePosition = value.rounds.front().challengeEventPosition;
    for (size_t input = 0; input < value.inputCount; ++input) {
      const auto &anchors = value.orderedInputAnchors[input];
      const auto &positions = value.orderedInputAnchorEventPositions[input];
      for (llvm::StringRef name : {"commitment", "point", "value"}) {
        auto anchor = anchors.find(name.str());
        auto position = positions.find(name.str());
        if (anchor == anchors.end() || anchor->second.empty() ||
            position == positions.end() ||
            position->second >= challengePosition)
          return false;
      }
    }
    return true;
  }
  case MachineDeciderKind::FriShape: {
    // The declared shape must be the realized one: n = k + log_blowup +
    // log_final_poly_len with log_blowup >= 1 (rate below one). This is
    // what stops a declared rate from drifting off the sealed schedule
    // and silently understating every bound priced from it.
    const registry::Rational &n = number(arguments[0]);
    const registry::Rational &k = number(arguments[1]);
    const registry::Rational &blowup = number(arguments[2]);
    const registry::Rational &finalLen = number(arguments[3]);
    if (blowup.compare(one) < 0 ||
        finalLen.compare(registry::Rational::fromInteger(0)) < 0)
      return false;
    return n.compare(k.add(blowup).add(finalLen)) == 0;
  }
  case MachineDeciderKind::JohnsonFoldParam:
    return number(arguments[0]).compare(registry::Rational::fromInteger(3)) >=
           0;
  case MachineDeciderKind::JohnsonSlack: {
    const registry::Rational &eta = number(arguments[0]);
    const registry::Rational &m = number(arguments[1]);
    const registry::Rational &blowup = number(arguments[2]);
    if (!positive(eta) || !positive(m) || blowup.compare(one) < 0)
      return false;
    auto sqrtRho = sqrtRhoBound(blowup, /*upper=*/false);
    if (!sqrtRho)
      return sqrtRho.takeError();
    auto bound = sqrtRho->div(m.mul(registry::Rational::fromInteger(2)));
    if (!bound)
      return bound.takeError();
    return eta.compare(*bound) < 0;
  }
  case MachineDeciderKind::JohnsonMultiplicity: {
    const registry::Rational &m = number(arguments[0]);
    const registry::Rational &eta = number(arguments[1]);
    const registry::Rational &blowup = number(arguments[2]);
    if (!positive(m) || !positive(eta) || blowup.compare(one) < 0)
      return false;
    auto sqrtRho = sqrtRhoBound(blowup, /*upper=*/true);
    if (!sqrtRho)
      return sqrtRho.takeError();
    return m.mul(eta)
               .mul(registry::Rational::fromInteger(2))
               .compare(*sqrtRho) >= 0;
  }
  case MachineDeciderKind::JohnsonDelta: {
    const registry::Rational &delta = number(arguments[0]);
    const registry::Rational &eta = number(arguments[1]);
    const registry::Rational &blowup = number(arguments[2]);
    if (!positive(delta) || blowup.compare(one) < 0)
      return false;
    auto sqrtRho = sqrtRhoBound(blowup, /*upper=*/true);
    if (!sqrtRho)
      return sqrtRho.takeError();
    registry::Rational cap = one.sub(*sqrtRho).sub(eta);
    return delta.compare(cap) < 0;
  }
  case MachineDeciderKind::RandomWordsEtaFloor: {
    // The Diamond-Gruen correction floor: eta_bar must not understate
    // (log2(e/rho) * rho) / log2 |F|. log2 e is bounded above by
    // 1443/1000 and log2 |F| below by ceil(log2 |F|) - 1, so the
    // floor computed here is at or above the true correction and a
    // passing eta_bar never understates the conjectured loss.
    const registry::Rational &etaBar = number(arguments[0]);
    const registry::Rational &declaredBlowup = number(arguments[1]);
    const registry::Rational &fieldOrder = number(arguments[2]);
    if (!positive(etaBar))
      return false;
    auto blowup = declaredBlowup.floorToInt();
    if (!blowup)
      return blowup.takeError();
    if (*blowup < 1 || *blowup > kMaxExactExponent)
      return deciderError("rate exponent exceeds the v0 exact range");
    auto rho = registry::Rational::fromInteger(2).pow(-*blowup);
    if (!rho)
      return rho.takeError();
    auto log2FieldCeil = fieldOrder.ceilLog2();
    if (!log2FieldCeil)
      return log2FieldCeil.takeError();
    int64_t log2FieldFloor = *log2FieldCeil - 1;
    if (log2FieldFloor < 1)
      return false;
    auto log2e = registry::Rational::fromDecimalPair("1443", "1000");
    if (!log2e)
      return log2e.takeError();
    registry::Rational numerator =
        log2e->add(registry::Rational::fromInteger(*blowup)).mul(*rho);
    auto floor =
        numerator.div(registry::Rational::fromInteger(log2FieldFloor));
    if (!floor)
      return floor.takeError();
    return etaBar.compare(*floor) >= 0;
  }
  case MachineDeciderKind::ThresholdDeltaWindow: {
    // The cited window (ePrint 2026/858): strictly above the Johnson
    // radius, strictly below 1 - rho. sqrt(rho) is bounded below by
    // its dyadic under-approximation, so the lower gate can only be
    // stricter than the theorem's own.
    const registry::Rational &delta = number(arguments[0]);
    const registry::Rational &declaredBlowup = number(arguments[1]);
    if (!positive(delta))
      return false;
    auto sqrtRhoLower = sqrtRhoBound(declaredBlowup, /*upper=*/false);
    if (!sqrtRhoLower)
      return sqrtRhoLower.takeError();
    auto blowup = declaredBlowup.floorToInt();
    if (!blowup)
      return blowup.takeError();
    if (*blowup < 1 || *blowup > kMaxExactExponent)
      return deciderError("rate exponent exceeds the v0 exact range");
    auto rho = registry::Rational::fromInteger(2).pow(-*blowup);
    if (!rho)
      return rho.takeError();
    registry::Rational johnson = one.sub(*sqrtRhoLower);
    registry::Rational cap = one.sub(*rho);
    return delta.compare(johnson) > 0 && delta.compare(cap) < 0;
  }
  case MachineDeciderKind::UdrDomainFloor: {
    // The cited corollary is stated for the fold-to-constant shape;
    // its last-round geometry reads n - k as the final domain, which
    // holds only at log_final_poly_len zero, so any early-stopping
    // declaration refuses here rather than pricing an overstated
    // last-round distance.
    const registry::Rational &n = number(arguments[0]);
    const registry::Rational &k = number(arguments[1]);
    const registry::Rational &finalLen = number(arguments[2]);
    if (n.compare(k) <= 0 ||
        finalLen.compare(registry::Rational::fromInteger(0)) != 0)
      return false;
    auto quantities = udrLastRound(n, k);
    if (!quantities)
      return quantities.takeError();
    const auto &[deltaLast, blockLength] = *quantities;
    return deltaLast.mul(deltaLast)
               .mul(blockLength)
               .compare(registry::Rational::fromInteger(18)) >= 0;
  }
  case MachineDeciderKind::UdrThetaWindow: {
    const registry::Rational &theta = number(arguments[0]);
    const registry::Rational &n = number(arguments[1]);
    const registry::Rational &k = number(arguments[2]);
    if (n.compare(k) <= 0)
      return false;
    auto quantities = udrLastRound(n, k);
    if (!quantities)
      return quantities.takeError();
    const auto &[deltaLast, blockLength] = *quantities;
    auto floor = deltaLast.div(registry::Rational::fromInteger(3));
    if (!floor)
      return floor.takeError();
    auto capLoss =
        registry::Rational::fromInteger(3).div(deltaLast.mul(blockLength));
    if (!capLoss)
      return capLoss.takeError();
    auto half = deltaLast.div(registry::Rational::fromInteger(2));
    if (!half)
      return half.takeError();
    registry::Rational cap = half->sub(*capLoss);
    return theta.compare(*floor) >= 0 && theta.compare(cap) <= 0;
  }
  case MachineDeciderKind::PowPinned: {
    // The adapter creates RoundAdjacencyValue only after resolving the
    // selected transparent check and proving that it pins this exact pow
    // challenge to a constant.  Check and value positions live in different
    // canonical index domains, so their integers must not be compared.
    (void)adjacency(arguments[0]);
    return true;
  }
  case MachineDeciderKind::PowAdjacent: {
    // Adjacency itself is established by the adapter, which withholds the
    // fact entirely when absorbed material sits between the pow challenge and
    // the protected one -- the free-resampling knob.  What is left to read
    // here is the ordering the two positions carry.
    const RoundAdjacencyValue &fact = adjacency(arguments[0]);
    return fact.premiseTransformerPosition < fact.grindingTransformerPosition &&
           fact.successorChallengeEventPosition >
               fact.powChallengeEventPosition;
  }
  case MachineDeciderKind::DuplexSpine: {
    const PathTransitionValue &transition = path(arguments[0]);
    if (!transition.duplexFacts)
      return false;
    auto biases = computeCodecBiases(*transition.duplexFacts);
    if (!biases)
      return biases.takeError();
    (void)biases;
    return transition.duplexFacts->segmentStarts.empty() &&
           !transition.duplexFacts->iv.empty();
  }
  case MachineDeciderKind::CodecBiasDeclared: {
    const PathTransitionValue &transition = path(arguments[0]);
    if (!transition.duplexFacts)
      return false;
    auto biases = computeCodecBiases(*transition.duplexFacts);
    if (!biases)
      return biases.takeError();
    return true;
  }
  }
  return deciderError("unknown machine-decider kind");
}

} // namespace zkc::soundness
