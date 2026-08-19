//===- PirSoundnessAdapter.cpp - Canonical PIR owned-view adapter ---------===//
#include "zkc/Soundness/PirSoundnessAdapter.h"

#include "Artifact/ArtifactInternal.h"
#include "zkc/Artifact/Artifact.h"
#include "zkc/ChallengeShape.h"
#include "zkc/Dialect/Pir/KappaView.h"
#include "zkc/Encoding/CanonicalEncoder.h"
#include "zkc/Encoding/EncodingDomain.h"
#include "zkc/Registry/ProtocolEnvironment.h"
#include "zkc/Semantics/ProtocolFacts.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/Support/Error.h"

#include <algorithm>
#include <limits>
#include <optional>
#include <utility>
#include <vector>

namespace zkc::soundness {
namespace {

llvm::Error adapterError(const llvm::Twine &detail) {
  return llvm::createStringError("sealed soundness adapter: " + detail);
}

llvm::Expected<ClaimRef>
lookupClaim(const llvm::DenseMap<mlir::Value, ClaimRef> &claimRefs,
            mlir::Value value) {
  auto claim = claimRefs.find(value);
  if (claim == claimRefs.end())
    return adapterError(
        "a reduction claim has no canonical claim-position entry");
  return claim->second;
}

mlir::DictionaryAttr claimAnchors(mlir::Value claim) {
  if (auto source = claim.getDefiningOp<pir::InstantiateOp>())
    return source.getAnchors();
  if (auto reduce = claim.getDefiningOp<pir::ReduceOp>()) {
    mlir::ArrayAttr outputAnchors =
        reduce.getOutAnchors().value_or(mlir::ArrayAttr());
    for (auto [index, output] : llvm::enumerate(reduce.getOuts()))
      if (output == claim && outputAnchors && index < outputAnchors.size())
        return mlir::dyn_cast<mlir::DictionaryAttr>(outputAnchors[index]);
  }
  return {};
}

llvm::Expected<std::map<std::string, std::string, std::less<>>>
copyClaimAnchors(mlir::Value claim) {
  std::map<std::string, std::string, std::less<>> result;
  mlir::DictionaryAttr anchors = claimAnchors(claim);
  if (!anchors)
    return result;
  for (mlir::NamedAttribute anchor : anchors) {
    auto value = mlir::dyn_cast<mlir::StringAttr>(anchor.getValue());
    if (!value)
      return adapterError("a consumed claim anchor is not a string");
    result.emplace(anchor.getName().getValue().str(), value.getValue().str());
  }
  return result;
}

llvm::Expected<uint64_t>
canonicalEventPosition(const encoding::CanonicalIndex &canonical,
                       mlir::Value value, const llvm::Twine &what) {
  auto found = canonical.eventPositions.find(value);
  if (found == canonical.eventPositions.end() || found->second < 0)
    return adapterError(what + " has no canonical event position");
  return static_cast<uint64_t>(found->second);
}

llvm::Expected<uint64_t>
canonicalCheckPosition(const encoding::CanonicalIndex &canonical,
                       pir::CheckOp check, const llvm::Twine &what) {
  auto found = canonical.checkPositions.find(check.getOperation());
  if (found == canonical.checkPositions.end() || found->second < 0)
    return adapterError(what + " has no canonical check-event position");
  return static_cast<uint64_t>(found->second);
}

llvm::Expected<pir::ChalOp>
roundChallenge(pir::ReduceOp reduce,
               const registry::ReductionContract &contract,
               llvm::StringRef role) {
  std::optional<size_t> selected;
  for (auto [index, slot] : llvm::enumerate(contract.depSlots)) {
    if (slot.role != role)
      continue;
    if (selected)
      return adapterError("a contract round challenge role names more than "
                          "one dependency slot");
    selected = index;
  }
  if (!selected || *selected >= reduce.getDeps().size())
    return adapterError("a contract round challenge role has no realized "
                        "dependency operand");
  auto challenge = reduce.getDeps()[*selected].getDefiningOp<pir::ChalOp>();
  if (!challenge)
    return adapterError("a contract round dependency is not a fresh "
                        "challenge event");
  return challenge;
}

llvm::Expected<registry::Rational> challengeSpace(pir::ChalOp challenge,
                                                  const llvm::Twine &what) {
  auto parsed = registry::Rational::fromDecimal(challenge.getSpace());
  if (!parsed)
    return adapterError(what + " has no exact challenge-space cardinality: " +
                        llvm::toString(parsed.takeError()));
  return *parsed;
}

llvm::Expected<uint64_t> challengeCount(pir::ChalOp challenge,
                                        const llvm::Twine &what) {
  std::optional<uint64_t> parsed =
      zkc::challenge::parseCount(challenge.getChallengeCount());
  if (!parsed)
    return adapterError(what + " has no exact challenge multiplicity");
  return *parsed;
}

llvm::Expected<std::pair<ChallengeShape, ChallengeSampling>>
challengeMode(pir::ChalOp challenge, const llvm::Twine &what) {
  if (!challenge.getMode()) {
    if (challenge.getChallengeCount() != "1" ||
        challenge.getChallengeSamplingRule() != "uniform")
      return adapterError(what + " has a malformed scalar sampling mode");
    return std::make_pair(ChallengeShape::Scalar, ChallengeSampling::Uniform);
  }
  if (challenge.getChallengeSamplingRule() != "uniform_independent")
    return adapterError(what + " has an unsupported vector sampling rule");
  return std::make_pair(ChallengeShape::Vector,
                        ChallengeSampling::UniformIndependent);
}

llvm::Expected<std::optional<registry::Rational>>
exactLog2(const registry::Rational &space) {
  auto exponent = space.ceilLog2();
  if (!exponent)
    return exponent.takeError();
  auto reconstructed = registry::Rational::fromInteger(2).pow(*exponent);
  if (!reconstructed)
    return reconstructed.takeError();
  if (reconstructed->compare(space) != 0)
    return std::optional<registry::Rational>();
  return std::optional<registry::Rational>(
      registry::Rational::fromInteger(*exponent));
}

llvm::Expected<SealedParameterAtom> parameterAtom(mlir::Attribute attribute,
                                                  const llvm::Twine &name) {
  if (auto value = mlir::dyn_cast<mlir::BoolAttr>(attribute))
    return SealedParameterAtom{SealedParameterAtom::Carrier::Boolean,
                               value.getValue()};
  if (auto value = mlir::dyn_cast<mlir::IntegerAttr>(attribute)) {
    if (!encoding::inIntegerDomain(value.getValue(),
                                   value.getType().isUnsignedInteger()))
      return adapterError(name + " is outside the canonical integer domain");
    return SealedParameterAtom{
        SealedParameterAtom::Carrier::Integer,
        registry::Rational::fromInteger(value.getValue().getSExtValue())};
  }
  if (auto value = mlir::dyn_cast<mlir::StringAttr>(attribute))
    return SealedParameterAtom{SealedParameterAtom::Carrier::String,
                               value.getValue().str()};
  return adapterError(name + " is not a soundness-visible scalar parameter");
}

llvm::Expected<SealedRoundFact>
buildRoundFact(pir::ReduceOp reduce,
               const registry::ReductionContract &contract,
               const registry::VocabularyRound &round, uint64_t roundPosition,
               const semantics::ProtocolFacts &protocolFacts,
               const encoding::CanonicalIndex &canonical) {
  auto challenge = roundChallenge(reduce, contract, round.challengeUse.role);
  if (!challenge)
    return challenge.takeError();

  auto eventPosition = canonicalEventPosition(
      canonical, challenge->getVal(),
      "reduction round " + llvm::Twine(roundPosition) + " challenge");
  if (!eventPosition)
    return eventPosition.takeError();
  auto space = challengeSpace(*challenge,
                              "reduction round " + llvm::Twine(roundPosition));
  if (!space)
    return space.takeError();
  auto count = challengeCount(*challenge,
                              "reduction round " + llvm::Twine(roundPosition));
  if (!count)
    return count.takeError();
  auto mode = challengeMode(*challenge,
                            "reduction round " + llvm::Twine(roundPosition));
  if (!mode)
    return mode.takeError();

  SealedRoundFact result;
  result.position = roundPosition;
  result.kind = round.kind;
  result.challengeRole = round.challengeUse.role;
  result.challengeEventPosition = *eventPosition;
  result.challengePayloadClass = challenge->getPayloadClass().str();
  result.challengeDomain = challenge->getDomain().str();
  result.challengeSpace = *space;
  result.challengeCount = *count;
  result.shape = mode->first;
  result.sampling = mode->second;

  auto instance = protocolFacts.memberships().find(reduce.getLabel());
  for (const registry::VocabularyMessageRole &message : round.messages) {
    SealedMessageRoleFact messageFact;
    messageFact.role = message.role;
    uint64_t multiplicity =
        message.multiplicity.resolve(reduce.getClaims().size());
    if (multiplicity >
        static_cast<uint64_t>(std::numeric_limits<int64_t>::max()))
      return adapterError("a round message multiplicity exceeds the canonical "
                          "occurrence-index domain");
    auto role = instance == protocolFacts.memberships().end()
                    ? nullptr
                    : &instance->second;
    auto occurrences =
        role ? role->find(message.role) : decltype(role->find(message.role))();
    if (!role || occurrences == role->end()) {
      if (multiplicity != 0)
        return adapterError("a contract round message role has no sealed "
                            "membership occurrences");
      result.messages.push_back(std::move(messageFact));
      continue;
    }
    messageFact.payloadClassesByOccurrence.reserve(multiplicity);
    for (uint64_t occurrence = 0; occurrence < multiplicity; ++occurrence) {
      auto members = protocolFacts.membershipOccurrences(
          reduce.getLabel(), message.role, static_cast<int64_t>(occurrence));
      if (members.empty())
        return adapterError("a contract round message role has a gap in its "
                            "sealed occurrence indices");
      if (members.size() != 1)
        return adapterError("a contract round message role has duplicate "
                            "sealed occurrence indices");
      // A role is filled by whatever carries the material: a slot for prover
      // messages, a public binding for content the statement fixes. Which of
      // the two a role admits is the contract's own declaration, checked
      // against the spine at seal, so the projection reads either.
      llvm::StringRef payloadClass;
      if (auto slot = mlir::dyn_cast<pir::SlotOp>(members.front()))
        payloadClass = slot.getPayloadClass();
      else if (auto bind = mlir::dyn_cast<pir::BindOp>(members.front()))
        payloadClass = bind.getPayloadClass();
      else
        return adapterError("a contract round message membership is neither a "
                            "prover message nor a public binding");
      messageFact.payloadClassesByOccurrence.push_back(payloadClass.str());
    }
    if (occurrences->second.size() != multiplicity)
      return adapterError("a contract round message role has extra sealed "
                          "membership occurrences");
    result.messages.push_back(std::move(messageFact));
  }

  // This is a structural projection of the exact contract realization, not a
  // fact selected by a theorem row.  Rules that require a degree will refuse
  // when the admitted one-role shape is absent.
  if (result.messages.size() == 1 &&
      result.messages.front().payloadClassesByOccurrence.size() >= 2) {
    result.roundDegree = registry::Rational::fromInteger(
        static_cast<int64_t>(
            result.messages.front().payloadClassesByOccurrence.size()) -
        1);
  }
  auto log2 = exactLog2(result.challengeSpace);
  if (!log2)
    return adapterError("cannot derive an exact challenge-space logarithm: " +
                        llvm::toString(log2.takeError()));
  result.challengeSpaceLog2 = std::move(*log2);
  return result;
}

mlir::Attribute expressionLeaf(mlir::Attribute node, llvm::StringRef tag) {
  auto array = mlir::dyn_cast_or_null<mlir::ArrayAttr>(node);
  if (!array || array.size() != 2)
    return {};
  auto actual = mlir::dyn_cast<mlir::StringAttr>(array[0]);
  if (!actual || actual.getValue() != tag)
    return {};
  return array[1];
}

bool pinsToConstant(pir::CheckOp check, mlir::Value challenge) {
  if (!check.getExpr())
    return false;
  mlir::ArrayAttr root = *check.getExpr();
  auto tag = root.size() == 3 ? mlir::dyn_cast<mlir::StringAttr>(root[0])
                              : mlir::StringAttr();
  if (!tag || tag.getValue() != "eq")
    return false;
  for (auto [inputSide, constantSide] :
       {std::pair{root[1], root[2]}, std::pair{root[2], root[1]}}) {
    auto input = mlir::dyn_cast_or_null<mlir::IntegerAttr>(
        expressionLeaf(inputSide, "in"));
    auto constant = mlir::dyn_cast_or_null<mlir::StringAttr>(
        expressionLeaf(constantSide, "const"));
    if (!input || !constant)
      continue;
    int64_t position = input.getInt();
    if (position >= 0 &&
        position < static_cast<int64_t>(check.getInputs().size()) &&
        check.getInputs()[position] == challenge)
      return true;
  }
  return false;
}

llvm::Expected<std::optional<RoundAdjacencyValue>>
buildRoundAdjacency(pir::ReduceOp reduce,
                    const registry::ReductionContract &contract,
                    const ExactRef &contractRef, uint64_t transformerPosition,
                    const llvm::DenseMap<mlir::Value, ClaimRef> &claimRefs,
                    const registry::ProtocolVocabulary &vocabulary,
                    const encoding::CanonicalIndex &canonical) {
  if (reduce.getClaims().size() != 1 || contract.rounds.size() != 1)
    return std::optional<RoundAdjacencyValue>();

  auto premiseClaim = lookupClaim(claimRefs, reduce.getClaims().front());
  if (!premiseClaim)
    return premiseClaim.takeError();
  auto producer = reduce.getClaims().front().getDefiningOp<pir::ReduceOp>();
  if (!producer)
    return std::optional<RoundAdjacencyValue>();
  auto premisePosition =
      canonical.transformerPositions.find(producer.getOperation());
  if (premisePosition == canonical.transformerPositions.end() ||
      premisePosition->second < 0)
    return adapterError("the grinding premise reduction has no canonical "
                        "transformer position");

  auto powChallenge = roundChallenge(reduce, contract,
                                     contract.rounds.front().challengeUse.role);
  if (!powChallenge)
    return powChallenge.takeError();
  auto powPosition = canonicalEventPosition(canonical, powChallenge->getVal(),
                                            "the grinding challenge");
  if (!powPosition)
    return powPosition.takeError();

  // What the grinding factor buys is that resampling the protected challenge
  // costs a fresh proof of work, and that holds only while nothing the prover
  // controls enters the transcript between the two.  An absorbed message in
  // between is a free knob: vary it and the protected challenge is redrawn
  // from a different sponge state at no cost, so one grind resamples without
  // limit and the round has not earned 2^-z.  Walking to the next challenge
  // and ignoring what lies between would admit exactly that spine.  Checks
  // are non-absorbing (kernel.md §1.1) and pass; any other member -- an
  // absorbed slot or a public bind -- withholds the fact, and a rule that
  // reads it then has no adjacency to scale by.
  pir::ChalOp successor;
  for (mlir::Operation *next = powChallenge->getOperation()->getNextNode();
       next; next = next->getNextNode()) {
    if (mlir::isa<pir::CheckOp>(next))
      continue;
    successor = mlir::dyn_cast<pir::ChalOp>(next);
    break;
  }
  if (!successor)
    return std::optional<RoundAdjacencyValue>();

  const registry::ReductionContract *premiseContract =
      vocabulary.lookupReductionContract(producer.getContract());
  if (!premiseContract)
    return adapterError("the grinding premise names no loaded reduction "
                        "contract");
  std::optional<uint64_t> premiseRoundPosition;
  for (auto [position, premiseRound] :
       llvm::enumerate(premiseContract->rounds)) {
    auto premiseChallenge = roundChallenge(producer, *premiseContract,
                                           premiseRound.challengeUse.role);
    if (!premiseChallenge)
      return premiseChallenge.takeError();
    if (premiseChallenge->getOperation() != successor.getOperation())
      continue;
    if (premiseRoundPosition)
      return adapterError("the grinding successor realizes more than one "
                          "premise round");
    premiseRoundPosition = position;
  }
  if (!premiseRoundPosition)
    return std::optional<RoundAdjacencyValue>();

  auto successorPosition = canonicalEventPosition(
      canonical, successor.getVal(), "the grinding successor challenge");
  if (!successorPosition)
    return successorPosition.takeError();

  if (!contract.checks.count("pow_pin"))
    return std::optional<RoundAdjacencyValue>();
  auto selectedPin = reduce.getChecks().getAs<mlir::StringAttr>("pow_pin");
  if (!selectedPin)
    return std::optional<RoundAdjacencyValue>();
  std::optional<uint64_t> pinPosition;
  for (mlir::Operation *user : powChallenge->getVal().getUsers()) {
    auto check = mlir::dyn_cast<pir::CheckOp>(user);
    if (!check || check.getLabel() != selectedPin.getValue() ||
        !pinsToConstant(check, powChallenge->getVal()))
      continue;
    auto position =
        canonicalCheckPosition(canonical, check, "the grinding pin check");
    if (!position)
      return position.takeError();
    if (!pinPosition || *position < *pinPosition)
      pinPosition = *position;
  }
  if (!pinPosition)
    return std::optional<RoundAdjacencyValue>();

  return std::optional<RoundAdjacencyValue>(RoundAdjacencyValue{
      contractRef,
      transformerPosition,
      std::move(*premiseClaim),
      static_cast<uint64_t>(premisePosition->second),
      *powPosition,
      *pinPosition,
      *successorPosition,
      *premiseRoundPosition,
  });
}

llvm::Expected<llvm::APInt> apFromDecimal(llvm::StringRef text) {
  if (text.empty() || !llvm::all_of(text, [](char value) {
        return value >= '0' && value <= '9';
      }))
    return adapterError("a construction-profile cardinality is not a decimal "
                        "integer");
  unsigned bits = llvm::APInt::getBitsNeeded(text, 10);
  return llvm::APInt(std::max(bits, 1u), text, 10);
}

struct BuiltCodecFact {
  SealedChallengeCodecFact fact;
  registry::Rational contribution;
};

/// Why one challenge cannot be modelled as a duplex squeeze, in the author's
/// terms.  Every early return below withdraws the whole artifact's duplex
/// facts, and a reader who only learns they are absent has to guess which of
/// the artifact's challenges to look at.
std::string unmodelable(pir::ChalOp challenge, const llvm::Twine &because) {
  return ("challenge '" + challenge.getLabel() + "' is not a duplex squeeze " +
          "this analysis can model: " + because)
      .str();
}

llvm::Expected<std::optional<BuiltCodecFact>>
buildCodecFact(pir::SealedOp sealed, pir::ChalOp challenge,
               const registry::SpongeProfile &sponge,
               const registry::ConstructionProfileRegistry &profiles,
               const encoding::CanonicalIndex &canonical,
               std::string &absence) {
  llvm::StringRef codecName =
      pir::kappaCodecName(sealed.getKappa(), challenge.getPayloadClass());
  const registry::CodecProfile *codec = profiles.lookupCodec(codecName);
  if (codecName.empty() || !codec || !codec->squeezes()) {
    absence = unmodelable(
        challenge, "its payload class '" + challenge.getPayloadClass() +
                       "' routes through codec '" + codecName +
                       "', which declares no squeeze");
    return std::optional<BuiltCodecFact>();
  }
  CodecKind codecKind;
  if (codec->squeezeKind == "mod_reduce")
    codecKind = CodecKind::ModReduce;
  else if (codec->squeezeKind == "tuple_bijection")
    codecKind = CodecKind::TupleBijection;
  else {
    absence = unmodelable(challenge, "codec '" + codecName +
                                         "' declares squeeze kind '" +
                                         codec->squeezeKind +
                                         "', which has no bias formula here");
    return std::optional<BuiltCodecFact>();
  }
  if (!encoding::isSha256Ref(codec->digest) || codec->squeezeSymbols <= 0)
    return adapterError("a squeeze codec has no exact admitted profile");

  auto alphabet = apFromDecimal(sponge.alphabetOrder);
  if (!alphabet)
    return alphabet.takeError();
  uint64_t widthNeeded =
      uint64_t(alphabet->getBitWidth()) * uint64_t(codec->squeezeSymbols) + 1;
  if (widthNeeded > (1u << 20))
    return adapterError("a squeeze domain exceeds the exact adapter width "
                        "limit");
  unsigned width = static_cast<unsigned>(widthNeeded);
  llvm::APInt domain(width, 1);
  llvm::APInt base = alphabet->zext(width);
  for (int64_t index = 0; index < codec->squeezeSymbols; ++index)
    domain *= base;

  auto rawSpace = apFromDecimal(challenge.getSpace());
  if (!rawSpace)
    return rawSpace.takeError();
  unsigned common = std::max(domain.getBitWidth(), rawSpace->getBitWidth());
  llvm::APInt n = domain.zext(common);
  llvm::APInt q = rawSpace->zext(common);
  if (q.isZero())
    return adapterError("a challenge has an empty sample space");

  auto decimal = [](const llvm::APInt &value) {
    llvm::SmallString<80> text;
    value.toString(text, 10, /*Signed=*/false);
    return std::string(text);
  };

  registry::Rational bias;
  if (codecKind == CodecKind::TupleBijection) {
    // A coordinate tuple is a uniform draw only for the target it bijects
    // with; a different target is unsupported, never silently reduced.
    if (q != n) {
      absence = unmodelable(
          challenge, "it samples " + decimal(q) + " through codec '" +
                         codecName + "', whose " +
                         std::to_string(codec->squeezeSymbols) +
                         " alphabet symbols biject with " + decimal(n) +
                         " exactly");
      return std::optional<BuiltCodecFact>();
    }
  } else {
    if (q.ugt(n)) {
      absence = unmodelable(challenge, "it samples " + decimal(q) +
                                           " through codec '" + codecName +
                                           "', whose " +
                                           std::to_string(
                                               codec->squeezeSymbols) +
                                           " squeeze symbols frame only " +
                                           decimal(n));
      return std::optional<BuiltCodecFact>();
    }
    llvm::APInt remainder = n.urem(q);
    if (!remainder.isZero()) {
      unsigned wide = 2 * common;
      llvm::APInt numerator = remainder.zext(wide) * (q - remainder).zext(wide);
      llvm::APInt denominator = n.zext(wide) * q.zext(wide);
      llvm::SmallString<64> numeratorText;
      llvm::SmallString<64> denominatorText;
      numerator.toString(numeratorText, 10, /*Signed=*/false);
      denominator.toString(denominatorText, 10, /*Signed=*/false);
      auto exact =
          registry::Rational::fromDecimalPair(numeratorText, denominatorText);
      if (!exact)
        return exact.takeError();
      bias = *exact;
    }
  }

  auto count = challengeCount(challenge, "duplex challenge");
  if (!count)
    return count.takeError();
  auto mode = challengeMode(challenge, "duplex challenge");
  if (!mode)
    return mode.takeError();
  auto space = challengeSpace(challenge, "duplex challenge");
  if (!space)
    return space.takeError();
  auto eventPosition = canonicalEventPosition(canonical, challenge.getVal(),
                                              "a duplex challenge");
  if (!eventPosition)
    return eventPosition.takeError();

  registry::Rational contribution =
      bias.mul(registry::Rational::fromInteger(static_cast<int64_t>(*count)));
  SealedChallengeCodecFact fact;
  fact.eventPosition = *eventPosition;
  fact.payloadClass = challenge.getPayloadClass().str();
  fact.domain = challenge.getDomain().str();
  fact.space = *space;
  fact.count = *count;
  fact.shape = mode->first;
  fact.sampling = mode->second;
  fact.codecRef = {codecName.str(), codec->digest};
  fact.codecKind = codecKind;
  fact.squeezeSymbols = static_cast<uint64_t>(codec->squeezeSymbols);
  fact.biasContribution = contribution;
  return std::optional<BuiltCodecFact>(
      BuiltCodecFact{std::move(fact), std::move(contribution)});
}

llvm::Expected<std::optional<SealedDuplexFacts>>
buildDuplexFacts(pir::SealedOp sealed,
                 const registry::ConstructionProfileRegistry &profiles,
                 const encoding::CanonicalIndex &canonical,
                 std::string &absence) {
  llvm::StringRef spongeName = pir::kappaSpongeName(sealed.getKappa());
  if (spongeName.empty()) {
    absence = "the sealed kappa names no sponge, so the artifact declares no "
              "duplex to squeeze from";
    return std::optional<SealedDuplexFacts>();
  }
  const registry::SpongeProfile *sponge = profiles.lookup(spongeName);
  if (!sponge)
    return adapterError("the sealed kappa names no loaded sponge profile");
  if (!encoding::isSha256Ref(sponge->digest) || sponge->capacity <= 0 ||
      sponge->rate <= 0)
    return adapterError("the sealed sponge has no exact admitted profile");
  auto alphabet = registry::Rational::fromDecimal(sponge->alphabetOrder);
  if (!alphabet)
    return adapterError("the sealed sponge alphabet is not exact: " +
                        llvm::toString(alphabet.takeError()));

  SealedDuplexFacts result;
  result.spongeRef = {spongeName.str(), sponge->digest};
  result.alphabetOrder = *alphabet;
  result.capacity = static_cast<uint64_t>(sponge->capacity);
  result.rate = static_cast<uint64_t>(sponge->rate);
  result.iv = pir::kappaIv(sealed.getKappa()).str();
  if (auto segments = sealed.getSegments())
    for (int64_t start : *segments) {
      if (start <= 0)
        return adapterError("a sealed segment start is not a positive event "
                            "position");
      result.segmentStarts.push_back(static_cast<uint64_t>(start));
    }

  for (mlir::Operation &operation : sealed.getBody().front()) {
    auto challenge = mlir::dyn_cast<pir::ChalOp>(operation);
    if (!challenge)
      continue;
    auto built = buildCodecFact(sealed, challenge, *sponge, profiles, canonical,
                                absence);
    if (!built)
      return built.takeError();
    // One challenge the analysis cannot model withdraws the facts for the
    // whole artifact: a bound assembled from the rest would price a
    // transcript with a squeeze missing from it.
    if (!*built)
      return std::optional<SealedDuplexFacts>();
    if (result.challenges.empty() ||
        result.codecBiasMax.compare((*built)->contribution) < 0)
      result.codecBiasMax = (*built)->contribution;
    result.codecBiasSum = result.codecBiasSum.add((*built)->contribution);
    result.challenges.push_back(std::move((*built)->fact));
  }
  llvm::sort(result.challenges, [](const SealedChallengeCodecFact &left,
                                   const SealedChallengeCodecFact &right) {
    return left.eventPosition < right.eventPosition;
  });
  return std::optional<SealedDuplexFacts>(std::move(result));
}

llvm::Expected<SealedSoundnessView> buildSealedSoundnessViewFromClone(
    pir::SealedOp sealed, llvm::StringRef admittedArtifactId,
    const registry::ProtocolVocabulary &vocabulary,
    const registry::ConstructionProfileRegistry &profiles) {
  if (!sealed)
    return adapterError("expected one pir.sealed operation");

  auto canonical = encoding::canonicalIndex(sealed.getOperation());
  if (!canonical)
    return canonical.takeError();
  semantics::ProtocolFacts protocolFacts =
      semantics::ProtocolFacts::compute(sealed.getBody().front());

  SealedSoundnessView view;
  view.artifactId = admittedArtifactId.str();
  view.policy = sealed.getPolicy().str();

  const size_t claimCount = canonical->claimPositions.size();
  if (canonical->claimDescriptors.size() != claimCount)
    return adapterError(
        "canonical claim positions and descriptors have different sizes");
  std::vector<std::optional<ClaimRef>> claimsByIndex(claimCount);
  llvm::DenseMap<mlir::Value, ClaimRef> claimRefs;
  claimRefs.reserve(claimCount);

  for (const auto &entry : canonical->claimPositions) {
    mlir::Value value = entry.first;
    int64_t signedPosition = entry.second;
    if (signedPosition < 0 ||
        static_cast<uint64_t>(signedPosition) >= claimCount)
      return adapterError("canonical claim position is not contiguous");

    auto descriptor = canonical->claimDescriptors.find(value);
    if (descriptor == canonical->claimDescriptors.end())
      return adapterError("canonical claim position has no descriptor digest");
    if (!encoding::isSha256Ref(descriptor->second))
      return adapterError("canonical claim descriptor is not a sha256 ref");

    uint64_t position = static_cast<uint64_t>(signedPosition);
    if (claimsByIndex[position])
      return adapterError("canonical claim position occurs more than once");
    ClaimRef ref{position, descriptor->second};
    claimsByIndex[position] = ref;
    if (!claimRefs.insert({value, std::move(ref)}).second)
      return adapterError("one claim value occurs more than once");
  }
  view.claimAnchorsByIndex.resize(claimCount);
  for (const auto &entry : canonical->claimPositions) {
    auto anchors = copyClaimAnchors(entry.first);
    if (!anchors)
      return anchors.takeError();
    view.claimAnchorsByIndex[static_cast<uint64_t>(entry.second)] =
        std::move(*anchors);
  }

  view.claimsByIndex.reserve(claimCount);
  for (std::optional<ClaimRef> &claim : claimsByIndex) {
    if (!claim)
      return adapterError("canonical claim positions contain a gap");
    view.claimsByIndex.push_back(std::move(*claim));
  }

  // The public statement ABI, in spine order: the same list, in the
  // same order, that projection turns into endpoint arguments.
  for (mlir::Operation &operation : sealed.getBody().front())
    if (auto bind = mlir::dyn_cast<pir::BindOp>(operation))
      if (bind.getStage() == pir::Stage::Instance)
        view.statementLabels.push_back(bind.getLabel().str());
      else if (std::optional<llvm::StringRef> value = bind.getValue())
        view.sealBindValues[bind.getLabel().str()] = value->str();

  llvm::StringMap<pir::CheckOp> checksByLabel;
  llvm::StringMap<uint64_t> materialEventPositions;
  for (mlir::Operation &operation : sealed.getBody().front()) {
    auto check = mlir::dyn_cast<pir::CheckOp>(operation);
    if (check && !checksByLabel.try_emplace(check.getLabel(), check).second)
      return adapterError("one sealed check label occurs more than once");
    auto material = mlir::dyn_cast<pir::MaterialBindOp>(operation);
    if (!material)
      continue;
    auto position = canonicalEventPosition(*canonical, material.getValue(),
                                           "a semantic material binding");
    if (!position)
      return position.takeError();
    view.boundMaterialRefs.insert(material.getSemanticRef().str());
    // The bound value's own label, where it has one: a statement
    // binding or a proof slot. Anything else stays unlabelled rather
    // than being given a manufactured name.
    if (mlir::Operation *producer = material.getValue().getDefiningOp()) {
      llvm::StringRef label;
      if (auto bind = mlir::dyn_cast<pir::BindOp>(producer))
        label = bind.getLabel();
      else if (auto slot = mlir::dyn_cast<pir::SlotOp>(producer))
        label = slot.getLabel();
      if (!label.empty())
        view.boundMaterialLabels[material.getSemanticRef().str()] = label.str();
    }
    if (!materialEventPositions
             .try_emplace(material.getSemanticRef(), *position)
             .second)
      return adapterError(
          "one semantic material reference names more than one event");
  }

  size_t reductionCount = 0;
  std::vector<TransformerExtent> transformerExtents;
  for (mlir::Operation &operation : sealed.getBody().front()) {
    auto reduce = mlir::dyn_cast<pir::ReduceOp>(operation);
    if (!reduce)
      continue;
    ++reductionCount;

    auto transformer =
        canonical->transformerPositions.find(reduce.getOperation());
    if (transformer == canonical->transformerPositions.end() ||
        transformer->second < 0)
      return adapterError(
          "sealed reduction has no canonical transformer position");
    uint64_t transformerPosition = static_cast<uint64_t>(transformer->second);

    const registry::ReductionContract *contract =
        vocabulary.lookupReductionContract(reduce.getContract());
    if (!contract)
      return adapterError("sealed reduction names no loaded contract");
    if (!encoding::isSha256Ref(contract->digest))
      return adapterError("loaded reduction contract has no exact digest");

    SealedReduction owned;
    owned.transformerPosition = transformerPosition;
    owned.contractRef = {reduce.getContract().str(), contract->digest};
    owned.orderedInputs.reserve(reduce.getClaims().size());
    owned.orderedOutputs.reserve(reduce.getOuts().size());

    for (mlir::Value input : reduce.getClaims()) {
      auto claim = lookupClaim(claimRefs, input);
      if (!claim)
        return claim.takeError();
      owned.orderedInputs.push_back(std::move(*claim));
      auto anchors = copyClaimAnchors(input);
      if (!anchors)
        return anchors.takeError();
      std::map<std::string, uint64_t, std::less<>> eventPositions;
      for (const auto &[name, anchor] : *anchors) {
        auto event = materialEventPositions.find(anchor);
        if (event != materialEventPositions.end())
          eventPositions.emplace(name, event->second);
      }
      owned.orderedInputAnchors.push_back(std::move(*anchors));
      owned.orderedInputAnchorEventPositions.push_back(
          std::move(eventPositions));
    }
    for (mlir::Value output : reduce.getOuts()) {
      auto claim = lookupClaim(claimRefs, output);
      if (!claim)
        return claim.takeError();
      owned.orderedOutputs.push_back(std::move(*claim));
    }

    mlir::DictionaryAttr parameters = reduce.getParams().value_or(
        mlir::DictionaryAttr::get(sealed.getContext()));
    for (mlir::NamedAttribute parameter : parameters) {
      auto value = parameterAtom(parameter.getValue(),
                                 "reduction parameter '" +
                                     parameter.getName().getValue() + "'");
      if (!value)
        return value.takeError();
      owned.parameters.emplace(parameter.getName().getValue().str(),
                               std::move(*value));
    }

    owned.rounds.reserve(contract->rounds.size());
    for (auto [roundPosition, round] : llvm::enumerate(contract->rounds)) {
      auto fact = buildRoundFact(reduce, *contract, round, roundPosition,
                                 protocolFacts, *canonical);
      if (!fact)
        return fact.takeError();
      owned.rounds.push_back(std::move(*fact));
    }

    // What the reduction's own commitments stand for. A profiled member
    // names a value profile; the profile says how much content is behind it,
    // and a rule that prices in that number reads it here rather than from a
    // producer's annotation. Collected per role, because which commitment is
    // the table and which is the looked-up column is a fact the contract
    // already states, and a lookup whose two sides differ in length has two
    // numbers to price from.
    {
      auto instanceRoles = protocolFacts.memberships().find(reduce.getLabel());
      if (instanceRoles != protocolFacts.memberships().end())
        for (const auto &role : instanceRoles->second) {
          std::set<std::string> arities;
          for (const auto &occurrence : role.getValue())
            for (mlir::Operation *member : occurrence.second) {
              // A member that declares nothing must not be silently passed
              // over. Skipping it would let a reduction profile one column
              // and leave another undeclared, and the arity a rule prices
              // with would then be whatever the profiled member said. The
              // empty string records "this role has a member with no
              // declared content", which the projection refuses on rather
              // than averaging over.
              llvm::StringRef profileName;
              if (auto slot = mlir::dyn_cast<pir::SlotOp>(member)) {
                if (slot.getProfiled())
                  profileName = slot.getPayloadClass();
              } else if (auto bind = mlir::dyn_cast<pir::BindOp>(member)) {
                if (bind.getProfiled())
                  profileName = bind.getPayloadClass();
              }
              if (profileName.empty()) {
                arities.insert(std::string());
                continue;
              }
              const registry::ValueProfile *profile =
                  vocabulary.lookupValueProfile(profileName);
              if (!profile)
                return adapterError(
                    "a profiled message member names a value profile the "
                    "sealed vocabulary does not declare");
              // One bit for the value and one for the shift's headroom, so
              // 2^64 -- the declared bound -- is exact rather than wrapping.
              llvm::APInt arity(static_cast<unsigned>(profile->arityLog2) + 2,
                                1);
              arity = arity.shl(static_cast<unsigned>(profile->arityLog2));
              llvm::SmallString<32> text;
              arity.toString(text, 10, /*Signed=*/false);
              arities.insert(std::string(text));
            }
          // Sorted numerically rather than by decimal text, so the order is
          // the one a reader expects and a tie cannot depend on digit count.
          llvm::SmallVector<registry::Rational> exactArities;
          bool incomplete = false;
          for (const std::string &text : arities) {
            if (text.empty()) {
              incomplete = true;
              continue;
            }
            auto exact = registry::Rational::fromDecimal(text);
            if (!exact)
              return exact.takeError();
            exactArities.push_back(std::move(*exact));
          }
          llvm::sort(exactArities, [](const registry::Rational &lhs,
                                      const registry::Rational &rhs) {
            return lhs.compare(rhs) < 0;
          });
          CommittedArityByRole entry;
          entry.role = role.getKey().str();
          entry.incomplete = incomplete;
          entry.arities.assign(exactArities.begin(), exactArities.end());
          owned.committedArityByRole.push_back(std::move(entry));
        }
      llvm::sort(owned.committedArityByRole,
                 [](const CommittedArityByRole &lhs,
                    const CommittedArityByRole &rhs) {
                   return lhs.role < rhs.role;
                 });
    }

    // The transformer's body extent, in canonical event positions.
    {
      TransformerExtent extent;
      extent.instance = reduce.getLabel().str();
      bool seen = false;
      auto observe = [&](uint64_t position) {
        extent.begin = seen ? std::min(extent.begin, position) : position;
        extent.end = seen ? std::max(extent.end, position) : position;
        seen = true;
      };
      auto instanceRoles = protocolFacts.memberships().find(reduce.getLabel());
      if (instanceRoles != protocolFacts.memberships().end())
        for (const auto &role : instanceRoles->second)
          for (const auto &occurrence : role.getValue())
            for (mlir::Operation *member : occurrence.second) {
              auto slot = mlir::dyn_cast<pir::SlotOp>(member);
              if (!slot)
                continue;
              auto position = canonicalEventPosition(
                  *canonical, slot.getVal(), "a reduction message member");
              if (!position)
                return position.takeError();
              observe(*position);
              if (slot.isAbsorbing())
                extent.central = false;
            }
      // A challenge the transformer's rounds sample is part of its body and
      // not merely a dependency: kernel §4's footprint is what a transformer
      // writes and what it reads, a message being an absorb and a challenge a
      // squeeze.  Sampling one is also exactly what makes a transformer
      // non-central.  Today no admitted contract can avoid one --
      // vocabularies.md requires a non-empty round list, because "a contract
      // with no interaction rounds states no local transition to judge or
      // price" -- so centrality is a constant in practice.  It is written as
      // the predicate the kernel states rather than as the constant it
      // currently evaluates to: the constant is a fact about the vocabulary,
      // the predicate is a fact about the category.
      for (const SealedRoundFact &round : owned.rounds) {
        observe(round.challengeEventPosition);
        extent.central = false;
      }
      if (seen)
        transformerExtents.push_back(std::move(extent));
    }

    for (mlir::NamedAttribute selection : reduce.getChecks()) {
      auto label = mlir::dyn_cast<mlir::StringAttr>(selection.getValue());
      if (!label)
        return adapterError("a reduction check selection is not a label");
      auto check = checksByLabel.find(label.getValue());
      if (check == checksByLabel.end())
        return adapterError("a reduction check selection names no sealed "
                            "check event");
      auto position = canonicalCheckPosition(
          *canonical, check->second,
          "reduction check role '" + selection.getName().getValue() + "'");
      if (!position)
        return position.takeError();
      owned.selectedCheckEventPositions.emplace(
          selection.getName().getValue().str(), *position);
    }

    auto adjacency = buildRoundAdjacency(reduce, *contract, owned.contractRef,
                                         transformerPosition, claimRefs,
                                         vocabulary, *canonical);
    if (!adjacency)
      return adjacency.takeError();
    owned.roundAdjacency = std::move(*adjacency);

    auto inserted = view.reductionsByTransformerPosition.emplace(
        transformerPosition, std::move(owned));
    if (!inserted.second)
      return adapterError(
          "canonical transformer position occurs more than once");
  }

  if (canonical->transformerPositions.size() != reductionCount ||
      view.reductionsByTransformerPosition.size() != reductionCount)
    return adapterError(
        "canonical transformer table does not cover every reduction exactly");

  // The bodies are projected, not judged. Whether an interleaved group
  // decomposes is the precondition of composing two claims in parallel, and
  // no shipped rule does that; accumulating a bound over a transcript is a
  // union bound over rounds, which interleaving does not threaten. The
  // artifact judgment is what asks whether every round was accounted for.
  llvm::sort(transformerExtents, bodyOrderLess);
  view.transformerBodies = std::move(transformerExtents);

  // Every squeeze the spine performs, whether or not a transformer owns it.
  // The artifact judgment reads this to ask whether a derivation accounted
  // for all of them; the duplex facts carry the same positions but exist
  // only when the sealed kappa names a sponge, and what rounds a bound must
  // cover is not a fact about the sponge profile.
  for (mlir::Operation &op : sealed.getBody().front())
    if (auto challenge = mlir::dyn_cast<pir::ChalOp>(op)) {
      auto position = canonicalEventPosition(*canonical, challenge.getVal(),
                                             "a challenge event");
      if (!position)
        return position.takeError();
      view.challengeEventPositions.push_back(*position);
    }
  llvm::sort(view.challengeEventPositions);

  auto duplex =
      buildDuplexFacts(sealed, profiles, *canonical, view.duplexAbsence);
  if (!duplex)
    return duplex.takeError();
  view.duplex = std::move(*duplex);
  if (view.duplex)
    view.duplexAbsence.clear();

  return view;
}

} // namespace

llvm::Expected<SealedSoundnessView>
buildSealedSoundnessView(const artifact::AdmittedPirArtifact &artifact) {
  const registry::ProtocolEnvironment &environment = artifact.environment();
  const registry::ConstructionProfileRegistry *profiles =
      environment.constructionProfiles();
  if (!profiles)
    return adapterError(
        "the admitted protocol environment has no construction profiles");

  artifact::detail::MutablePirArtifact clone =
      artifact::detail::ArtifactAccess::cloneForReopen(artifact);
  return buildSealedSoundnessViewFromClone(clone.sealed(), artifact.id(),
                                           environment.protocolVocabulary(),
                                           *profiles);
}

} // namespace zkc::soundness
