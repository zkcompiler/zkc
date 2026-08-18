//===- TransformerGroupTest.cpp - kernel §4's decomposition decision ------===//
// An interleaved group decomposes per-transformer exactly when all but one
// of its members is central (docs/spec/kernel.md §4).  The admitting half of
// that criterion is unreachable from any admissible artifact -- a reduction
// contract must declare at least one round, so every admitted transformer
// samples a challenge and none is central -- which is exactly why it is
// tested here, at the predicate, rather than through a fixture that cannot
// be authored.
//===----------------------------------------------------------------------===//

#include "zkc/Soundness/SealedSoundnessView.h"

#include "llvm/Support/Error.h"
#include "ZkcTest.h"

#include <string>
#include <utility>
#include <vector>

using namespace zkc::soundness;

namespace {

TransformerExtent extent(std::string instance, uint64_t begin, uint64_t end,
                         bool central) {
  TransformerExtent value;
  value.instance = std::move(instance);
  value.begin = begin;
  value.end = end;
  value.central = central;
  return value;
}

/// The refusal's message, or the empty string when the groups decompose.
std::string decide(std::vector<TransformerExtent> extents) {
  llvm::Error error = requireDecomposableTransformerGroups(std::move(extents));
  if (!error)
    return "";
  return llvm::toString(std::move(error));
}

TEST(TransformerGroups, DisjointExtentsDecompose) {
  EXPECT_EQ(decide({extent("a", 0, 2, false), extent("b", 3, 5, false)}), "");
}

TEST(TransformerGroups, TwoNonCentralMembersOfOneGroupRefuse) {
  std::string refusal =
      decide({extent("a", 0, 4, false), extent("b", 2, 6, false)});
  EXPECT_TRUE(refusal.find("'a' and 'b' are both non-central") !=
              std::string::npos);
  EXPECT_TRUE(refusal.find("does not decompose per-transformer") !=
              std::string::npos);
}

TEST(TransformerGroups, OneNonCentralMemberDecomposes) {
  // The admitting half of kernel §4: a central transformer interleaved
  // around one that carries the transcript effect still decomposes.
  EXPECT_EQ(decide({extent("bookkeeping", 0, 9, true),
                    extent("real", 2, 6, false)}),
            "");
}

TEST(TransformerGroups, CentralMembersAloneDecompose) {
  EXPECT_EQ(decide({extent("a", 0, 9, true), extent("b", 1, 8, true),
                    extent("c", 2, 7, true)}),
            "");
}

TEST(TransformerGroups, GroupsAreTransitiveNotPairwise) {
  // 'a' and 'c' do not overlap each other, but both overlap the central
  // 'bridge', so the three are one group with two non-central members.  A
  // pairwise test would admit this; the group criterion does not.
  std::string refusal = decide({extent("a", 0, 3, false),
                                extent("bridge", 2, 7, true),
                                extent("c", 6, 9, false)});
  EXPECT_TRUE(refusal.find("are both non-central") != std::string::npos);
}

TEST(TransformerGroups, ASingleTransformerNeverRefuses) {
  EXPECT_EQ(decide({extent("only", 0, 9, false)}), "");
  EXPECT_EQ(decide({}), "");
}

TEST(TransformerGroups, AdjacentExtentsTouchingAtAPositionAreOneGroup) {
  // Sharing a position is overlap: the two bodies are not separable in
  // spine order, so the group criterion applies to them.
  std::string refusal =
      decide({extent("a", 0, 3, false), extent("b", 3, 6, false)});
  EXPECT_TRUE(refusal.find("are both non-central") != std::string::npos);
}

TEST(TransformerGroups, SeparateGroupsAreJudgedSeparately) {
  // Two groups, each with one non-central member: both decompose, and the
  // count does not leak across the gap between them.
  EXPECT_EQ(decide({extent("a", 0, 3, false), extent("pad_a", 1, 2, true),
                    extent("b", 10, 13, false), extent("pad_b", 11, 12, true)}),
            "");
}

TEST(TransformerGroups, EqualExtentsAreOrderedDeterministically) {
  // `llvm::sort` is not stable, so the instance name is part of the sort key.
  // Without it the two members named by the refusal would be whichever the
  // sort happened to leave first, differing between runs and between the two
  // implementations.
  std::string forward =
      decide({extent("b", 0, 4, false), extent("a", 0, 4, false)});
  std::string reverse =
      decide({extent("a", 0, 4, false), extent("b", 0, 4, false)});
  EXPECT_EQ(forward, reverse);
  EXPECT_TRUE(forward.find("'a' and 'b'") != std::string::npos);
}

TEST(TransformerGroups, AGroupNestedInsideAnotherIsOneGroup) {
  // Containment is overlap: a transformer whose extent sits wholly inside
  // another's is interleaved with it, and the running group end must not be
  // pulled backwards by the shorter one.
  std::string refusal = decide({extent("outer", 0, 20, false),
                                extent("inner", 5, 6, false),
                                extent("after", 18, 25, true)});
  EXPECT_TRUE(refusal.find("are both non-central") != std::string::npos);
}

TEST(TransformerGroups, AContainedCentralMemberDoesNotSplitTheGroup) {
  // The same containment shape, but the inner member commutes: the group is
  // still one group, and it still decomposes.
  EXPECT_EQ(decide({extent("outer", 0, 20, false), extent("inner", 5, 6, true),
                    extent("later", 30, 40, false)}),
            "");
}

TEST(TransformerGroups, SinglePositionExtentsAreComparable) {
  // A transformer owning exactly one event has begin == end. Two of them at
  // the same position cannot arise from slot ownership, but the predicate is
  // defined over extents rather than over what produced them.
  EXPECT_EQ(decide({extent("a", 7, 7, false), extent("b", 9, 9, false)}), "");
  std::string refusal =
      decide({extent("a", 7, 7, false), extent("b", 7, 7, false)});
  EXPECT_TRUE(refusal.find("are both non-central") != std::string::npos);
}

} // namespace
