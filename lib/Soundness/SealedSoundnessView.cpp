//===- SealedSoundnessView.cpp - Exact owned subject resolution ----------===//
#include "zkc/Soundness/SealedSoundnessView.h"

#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"

#include <algorithm>
#include <set>
#include <utility>

namespace zkc::soundness {

bool operator==(const ClaimRef &lhs, const ClaimRef &rhs) {
  return lhs.claimIndex == rhs.claimIndex &&
         lhs.descriptorDigest == rhs.descriptorDigest;
}

bool operator!=(const ClaimRef &lhs, const ClaimRef &rhs) {
  return !(lhs == rhs);
}

bool operator==(const ProtocolClaimSubject &lhs,
                const ProtocolClaimSubject &rhs) {
  return lhs.artifactId == rhs.artifactId && lhs.claim == rhs.claim;
}

bool operator!=(const ProtocolClaimSubject &lhs,
                const ProtocolClaimSubject &rhs) {
  return !(lhs == rhs);
}

bool operator==(const ConsumedClaimVectorSubject &lhs,
                const ConsumedClaimVectorSubject &rhs) {
  return lhs.artifactId == rhs.artifactId && lhs.consumer == rhs.consumer &&
         lhs.orderedSources == rhs.orderedSources;
}

bool operator!=(const ConsumedClaimVectorSubject &lhs,
                const ConsumedClaimVectorSubject &rhs) {
  return !(lhs == rhs);
}

namespace {

bool rationalEqual(const registry::Rational &lhs,
                   const registry::Rational &rhs) {
  return lhs.compare(rhs) == 0;
}

bool optionalRationalEqual(const std::optional<registry::Rational> &lhs,
                           const std::optional<registry::Rational> &rhs) {
  return lhs.has_value() == rhs.has_value() &&
         (!lhs || rationalEqual(*lhs, *rhs));
}

} // namespace

bool operator==(const SealedMessageRoleFact &lhs,
                const SealedMessageRoleFact &rhs) {
  return lhs.role == rhs.role &&
         lhs.payloadClassesByOccurrence == rhs.payloadClassesByOccurrence;
}

bool operator==(const SealedRoundFact &lhs, const SealedRoundFact &rhs) {
  return lhs.position == rhs.position && lhs.kind == rhs.kind &&
         lhs.challengeRole == rhs.challengeRole &&
         lhs.challengeEventPosition == rhs.challengeEventPosition &&
         lhs.challengePayloadClass == rhs.challengePayloadClass &&
         lhs.challengeDomain == rhs.challengeDomain &&
         rationalEqual(lhs.challengeSpace, rhs.challengeSpace) &&
         lhs.challengeCount == rhs.challengeCount && lhs.shape == rhs.shape &&
         lhs.sampling == rhs.sampling && lhs.messages == rhs.messages &&
         optionalRationalEqual(lhs.roundDegree, rhs.roundDegree) &&
         optionalRationalEqual(lhs.challengeSpaceLog2, rhs.challengeSpaceLog2);
}

bool operator==(const SealedParameterAtom &lhs,
                const SealedParameterAtom &rhs) {
  if (lhs.carrier != rhs.carrier || lhs.value.index() != rhs.value.index())
    return false;
  if (const auto *left = std::get_if<registry::Rational>(&lhs.value)) {
    const auto *right = std::get_if<registry::Rational>(&rhs.value);
    return right && rationalEqual(*left, *right);
  }
  if (const auto *left = std::get_if<std::string>(&lhs.value)) {
    const auto *right = std::get_if<std::string>(&rhs.value);
    return right && *left == *right;
  }
  const auto *left = std::get_if<bool>(&lhs.value);
  const auto *right = std::get_if<bool>(&rhs.value);
  return left && right && *left == *right;
}

bool operator==(const RoundAdjacencyValue &lhs,
                const RoundAdjacencyValue &rhs) {
  return lhs.contractRef == rhs.contractRef &&
         lhs.grindingTransformerPosition == rhs.grindingTransformerPosition &&
         lhs.premiseClaim == rhs.premiseClaim &&
         lhs.premiseTransformerPosition == rhs.premiseTransformerPosition &&
         lhs.powChallengeEventPosition == rhs.powChallengeEventPosition &&
         lhs.pinCheckEventPosition == rhs.pinCheckEventPosition &&
         lhs.successorChallengeEventPosition ==
             rhs.successorChallengeEventPosition &&
         lhs.premiseRoundPosition == rhs.premiseRoundPosition;
}

bool operator==(const SealedChallengeCodecFact &lhs,
                const SealedChallengeCodecFact &rhs) {
  return lhs.eventPosition == rhs.eventPosition &&
         lhs.payloadClass == rhs.payloadClass && lhs.domain == rhs.domain &&
         rationalEqual(lhs.space, rhs.space) && lhs.count == rhs.count &&
         lhs.shape == rhs.shape && lhs.sampling == rhs.sampling &&
         lhs.codecRef == rhs.codecRef && lhs.codecKind == rhs.codecKind &&
         lhs.squeezeSymbols == rhs.squeezeSymbols &&
         rationalEqual(lhs.biasContribution, rhs.biasContribution);
}

bool operator==(const SealedDuplexFacts &lhs, const SealedDuplexFacts &rhs) {
  return lhs.spongeRef == rhs.spongeRef &&
         rationalEqual(lhs.alphabetOrder, rhs.alphabetOrder) &&
         lhs.capacity == rhs.capacity && lhs.rate == rhs.rate &&
         lhs.iv == rhs.iv && lhs.segmentStarts == rhs.segmentStarts &&
         lhs.challenges == rhs.challenges &&
         rationalEqual(lhs.codecBiasMax, rhs.codecBiasMax) &&
         rationalEqual(lhs.codecBiasSum, rhs.codecBiasSum);
}

namespace {

llvm::Error resolutionError(const llvm::Twine &detail) {
  return llvm::createStringError("sealed soundness view: " + detail);
}

llvm::Error requireArtifact(const SealedSoundnessView &sealed,
                            const std::string &siteArtifactId) {
  if (sealed.artifactId.empty())
    return resolutionError("the sealed artifact id is empty");
  if (siteArtifactId != sealed.artifactId)
    return resolutionError("application site names a different artifact: "
                           "sealed " +
                           sealed.artifactId + ", site cites " +
                           siteArtifactId);
  return llvm::Error::success();
}

llvm::Error requireClaimMember(const SealedSoundnessView &sealed,
                               const ClaimRef &claim) {
  if (claim.claimIndex >= sealed.claimsByIndex.size())
    return resolutionError("claim index is outside the sealed claim table");
  if (sealed.claimsByIndex[claim.claimIndex] != claim)
    return resolutionError(
        "claim descriptor does not match its canonical claim index");
  return llvm::Error::success();
}

llvm::Expected<const SealedReduction *>
resolveReduction(const SealedSoundnessView &sealed,
                 const ReductionOccurrence &site) {
  if (llvm::Error error = requireArtifact(sealed, site.artifactId))
    return std::move(error);
  auto reduction =
      sealed.reductionsByTransformerPosition.find(site.transformerPosition);
  if (reduction == sealed.reductionsByTransformerPosition.end())
    return resolutionError(
        "canonical transformer position names no sealed reduction");
  if (reduction->second.transformerPosition != site.transformerPosition)
    return resolutionError("reduction table key and owned position disagree");
  return &reduction->second;
}

llvm::Expected<ConsumedClaimVectorSubject>
makeConsumedSubject(const SealedSoundnessView &sealed,
                    const ReductionOccurrence &site,
                    const std::vector<uint64_t> &inputIndices) {
  if (inputIndices.empty())
    return resolutionError("a consumed-claim vector cannot be empty");

  auto reduction = resolveReduction(sealed, site);
  if (!reduction)
    return reduction.takeError();
  auto consumer = resolveReductionOutput(sealed, site);
  if (!consumer)
    return consumer.takeError();

  std::set<uint64_t> seen;
  std::vector<ClaimRef> sources;
  sources.reserve(inputIndices.size());
  for (uint64_t inputIndex : inputIndices) {
    if (!seen.insert(inputIndex).second)
      return resolutionError(
          "explicit consumed-input positions must be duplicate-free");
    if (inputIndex >= (*reduction)->orderedInputs.size())
      return resolutionError(
          "consumed-input position is outside the reduction input vector");
    const ClaimRef &input = (*reduction)->orderedInputs[inputIndex];
    if (llvm::Error error = requireClaimMember(sealed, input))
      return std::move(error);
    sources.push_back(input);
  }

  return ConsumedClaimVectorSubject{sealed.artifactId, std::move(*consumer),
                                    std::move(sources)};
}

} // namespace

llvm::Error
requireDecomposableTransformerGroups(std::vector<TransformerExtent> extents) {
  if (extents.size() < 2)
    return llvm::Error::success();
  // The instance name is part of the key, not decoration: `llvm::sort` is
  // not stable, so without it two transformers with equal extents would be
  // named in an unspecified order and the refusal would differ between runs
  // and between implementations.  The twin sorts by the same triple.
  llvm::sort(extents, [](const TransformerExtent &lhs,
                         const TransformerExtent &rhs) {
    return std::tie(lhs.begin, lhs.end, lhs.instance) <
           std::tie(rhs.begin, rhs.end, rhs.instance);
  });

  size_t groupStart = 0;
  uint64_t groupEnd = extents.front().end;
  auto closeGroup = [&](size_t pastEnd) -> llvm::Error {
    llvm::SmallVector<llvm::StringRef> nonCentral;
    for (size_t index = groupStart; index < pastEnd; ++index)
      if (!extents[index].central)
        nonCentral.push_back(extents[index].instance);
    if (nonCentral.size() < 2)
      return llvm::Error::success();
    return llvm::createStringError(
        "sealed soundness adapter: interleaved reduction bodies '" +
        nonCentral[0] + "' and '" + nonCentral[1] +
        "' are both non-central, so the group does not decompose "
        "per-transformer and requires an exact composite soundness rule");
  };

  for (size_t index = 1; index < extents.size(); ++index) {
    if (extents[index].begin <= groupEnd) {
      groupEnd = std::max(groupEnd, extents[index].end);
      continue;
    }
    if (llvm::Error error = closeGroup(index))
      return error;
    groupStart = index;
    groupEnd = extents[index].end;
  }
  return closeGroup(extents.size());
}

ArtifactJudgment judgeArtifact(const SealedSoundnessView &sealed,
                               const ClaimRef &targetClaim) {
  ArtifactJudgment judgment;
  judgment.policy = sealed.policy;

  // A claim some reduction consumes is carried onward by that reduction
  // rather than left standing, so it is not the artifact's conclusion.
  std::set<uint64_t> consumed;
  for (const auto &[position, reduction] :
       sealed.reductionsByTransformerPosition) {
    (void)position;
    for (const ClaimRef &input : reduction.orderedInputs)
      consumed.insert(input.claimIndex);
  }

  // The target has to be a claim of this artifact at all: a derivation
  // about a claim index this artifact does not carry, or about a
  // descriptor it does not carry at that index, discharges nothing,
  // however sound each of its steps was.
  const bool targetIsOurs =
      targetClaim.claimIndex < sealed.claimsByIndex.size() &&
      sealed.claimsByIndex[targetClaim.claimIndex] == targetClaim;

  // Covered by the target only when the target really is that claim: a
  // ref whose index exists but whose descriptor does not would
  // otherwise excuse the one claim actually left standing, and the
  // report would name no reason for a judgment that is already
  // negative.
  for (uint64_t index = 0; index < sealed.claimsByIndex.size(); ++index) {
    if (consumed.count(index) ||
        (targetIsOurs && index == targetClaim.claimIndex))
      continue;
    judgment.uncoveredClaims.push_back(index);
  }

  judgment.discharged = targetIsOurs && judgment.uncoveredClaims.empty() &&
                        sealed.policy == "closed_proof";
  return judgment;
}

llvm::Expected<ClaimRef>
resolveReductionOutput(const SealedSoundnessView &sealed,
                       const ReductionOccurrence &site) {
  auto reduction = resolveReduction(sealed, site);
  if (!reduction)
    return reduction.takeError();
  if (site.outputIndex >= (*reduction)->orderedOutputs.size())
    return resolutionError(
        "output index is outside the sealed reduction output vector");

  const ClaimRef &resolved = (*reduction)->orderedOutputs[site.outputIndex];
  if (llvm::Error error = requireClaimMember(sealed, resolved))
    return std::move(error);
  if (resolved != site.ownerClaim)
    return resolutionError(
        "owner claim does not equal the canonically resolved output: "
        "resolved " +
        resolved.descriptorDigest + ", site cites " +
        site.ownerClaim.descriptorDigest);
  return resolved;
}

llvm::Expected<ProtocolClaimSubject>
subjectOf(const SealedSoundnessView &sealed, const ApplicationSite &site) {
  if (const auto *reduction = std::get_if<ReductionOccurrence>(&site)) {
    auto claim = resolveReductionOutput(sealed, *reduction);
    if (!claim)
      return claim.takeError();
    return ProtocolClaimSubject{sealed.artifactId, std::move(*claim)};
  }

  const PathOccurrence &path = std::get<PathOccurrence>(site);
  if (llvm::Error error = requireArtifact(sealed, path.artifactId))
    return std::move(error);
  if (llvm::Error error = requireClaimMember(sealed, path.claim))
    return std::move(error);
  return ProtocolClaimSubject{sealed.artifactId, path.claim};
}

llvm::Expected<ProtocolClaimSubject>
resolveReductionInput(const SealedSoundnessView &sealed,
                      const ReductionOccurrence &site, uint64_t inputIndex) {
  auto consumer = resolveReductionOutput(sealed, site);
  if (!consumer)
    return consumer.takeError();
  auto reduction = resolveReduction(sealed, site);
  if (!reduction)
    return reduction.takeError();
  if (inputIndex >= (*reduction)->orderedInputs.size())
    return resolutionError(
        "input index is outside the sealed reduction input vector");
  const ClaimRef &input = (*reduction)->orderedInputs[inputIndex];
  if (llvm::Error error = requireClaimMember(sealed, input))
    return std::move(error);
  return ProtocolClaimSubject{sealed.artifactId, input};
}

llvm::Expected<ConsumedClaimVectorSubject>
resolveAllReductionInputs(const SealedSoundnessView &sealed,
                          const ReductionOccurrence &site) {
  auto reduction = resolveReduction(sealed, site);
  if (!reduction)
    return reduction.takeError();
  std::vector<uint64_t> indices;
  indices.reserve((*reduction)->orderedInputs.size());
  for (uint64_t index = 0; index < (*reduction)->orderedInputs.size(); ++index)
    indices.push_back(index);
  return makeConsumedSubject(sealed, site, indices);
}

llvm::Expected<ConsumedClaimVectorSubject>
resolveReductionInputs(const SealedSoundnessView &sealed,
                       const ReductionOccurrence &site,
                       const std::vector<uint64_t> &inputIndices) {
  return makeConsumedSubject(sealed, site, inputIndices);
}

} // namespace zkc::soundness
