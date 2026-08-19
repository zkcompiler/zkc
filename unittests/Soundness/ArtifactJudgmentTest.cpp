//===- ArtifactJudgmentTest.cpp - round coverage over an artifact ---------===//
// A derivation concludes about one claim; the artifact judgment says whether
// it covers the artifact.  A round-by-round bound reaches a protocol by a
// union bound over its rounds, so a challenge no covered transformer owns is
// a term the sum omits, and an artifact-level claim resting on that sum
// prices a protocol that is not this one.
//
// The coverage walk and the judgment are separate functions so that this
// half can be exercised without building a derivation.
//===----------------------------------------------------------------------===//

#include "zkc/Soundness/SealedSoundnessView.h"

#include "ZkcTest.h"

#include <string>
#include <vector>

using namespace zkc::soundness;

namespace {

ClaimRef claim(uint64_t index) {
  ClaimRef ref;
  ref.claimIndex = index;
  ref.descriptorDigest = "sha256:" + std::to_string(index);
  return ref;
}

/// Two transformers, one challenge each, one claim apiece consumed onward:
/// claim 0 into transformer 0, claim 1 into transformer 1, and the two
/// conclusions left standing at claim 2 and claim 3.
SealedSoundnessView twoTransformers() {
  SealedSoundnessView view;
  view.artifactId = "artifact";
  view.policy = "closed_proof";
  for (uint64_t index = 0; index < 4; ++index)
    view.claimsByIndex.push_back(claim(index));
  view.challengeEventPositions = {10, 11};
  for (uint64_t position = 0; position < 2; ++position) {
    SealedReduction reduction;
    reduction.transformerPosition = position;
    reduction.orderedInputs = {claim(position)};
    reduction.orderedOutputs = {claim(position + 2)};
    SealedRoundFact round;
    round.challengeEventPosition = 10 + position;
    reduction.rounds.push_back(round);
    view.reductionsByTransformerPosition.emplace(position,
                                                 std::move(reduction));
  }
  return view;
}

DerivationCoverage covering(std::set<uint64_t> transformers,
                            SecurityTrack track) {
  DerivationCoverage coverage;
  coverage.coveredTransformers = std::move(transformers);
  coverage.track = track;
  return coverage;
}

TEST(ArtifactJudgment, AnUnownedRoundIsNamedAndBlocksDischarge) {
  SealedSoundnessView view = twoTransformers();
  ArtifactJudgment judgment =
      judgeArtifact(view, claim(2), covering({0}, SecurityTrack::Soundness));
  EXPECT_EQ(judgment.uncoveredChallenges.size(), 1u);
  EXPECT_EQ(judgment.uncoveredChallenges.front(), 11u);
  EXPECT_FALSE(judgment.discharged);
}

TEST(ArtifactJudgment, CoveringEveryTransformerLeavesNoRoundUnindexed) {
  SealedSoundnessView view = twoTransformers();
  // Claim 3 is still left standing, so this is not discharged either -- but
  // for the claim, and the rounds are all accounted for.
  ArtifactJudgment judgment = judgeArtifact(
      view, claim(2), covering({0, 1}, SecurityTrack::Soundness));
  EXPECT_TRUE(judgment.uncoveredChallenges.empty());
  EXPECT_EQ(judgment.uncoveredClaims.size(), 1u);
}

TEST(ArtifactJudgment, KnowledgeAccumulatesLikeSoundness) {
  SealedSoundnessView view = twoTransformers();
  ArtifactJudgment judgment =
      judgeArtifact(view, claim(2), covering({0}, SecurityTrack::Knowledge));
  EXPECT_EQ(judgment.uncoveredChallenges.size(), 1u);
}

TEST(ArtifactJudgment, CompletenessAccumulatesNothingOverTheTranscript) {
  // A completeness judgment makes no claim assembled from per-round costs,
  // so the rounds are not its to account for. The exemption is a decision,
  // which is why it is stated here rather than left to the absence of a
  // check.
  SealedSoundnessView view = twoTransformers();
  ArtifactJudgment judgment = judgeArtifact(
      view, claim(2), covering({0}, SecurityTrack::Completeness));
  EXPECT_TRUE(judgment.uncoveredChallenges.empty());
}

TEST(ArtifactJudgment, AChallengeNoTransformerOwnsIsNeverCovered) {
  // A squeeze outside every transformer's rounds is one nobody prices, and
  // no derivation can reach it. Sealing admits such an artifact; claiming it
  // is discharged is what this refuses.
  SealedSoundnessView view = twoTransformers();
  view.challengeEventPositions.push_back(12);
  ArtifactJudgment judgment = judgeArtifact(
      view, claim(2), covering({0, 1}, SecurityTrack::Soundness));
  EXPECT_EQ(judgment.uncoveredChallenges.size(), 1u);
  EXPECT_EQ(judgment.uncoveredChallenges.front(), 12u);
}

TEST(ArtifactJudgment, RoundsAreNamedInCanonicalOrder) {
  SealedSoundnessView view = twoTransformers();
  ArtifactJudgment judgment =
      judgeArtifact(view, claim(2), covering({}, SecurityTrack::Soundness));
  EXPECT_EQ(judgment.uncoveredChallenges,
            (std::vector<uint64_t>{10u, 11u}));
}

} // namespace
