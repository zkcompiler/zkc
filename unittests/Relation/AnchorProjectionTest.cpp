//===- AnchorProjectionTest.cpp - The transcript projection -----*- C++ -*-===//
// docs/spec/relations.md §2.8. The projection's whole job is to be a
// function of the anchor alone whose every element is canonical for the
// field its class frames — so the properties are what is tested, not a
// handful of remembered outputs.
//===----------------------------------------------------------------------===//

#include "zkc/Relation/AnchorProjection.h"

#include "llvm/ADT/APInt.h"
#include "llvm/Support/Error.h"
#include "ZkcTest.h"

#include <string>
#include <vector>

using namespace zkc::relation;

namespace {

/// A `sha256:` reference over a repeating nibble pattern, so a test can
/// name an anchor without carrying a digest nobody can read.
std::string anchorOf(llvm::StringRef pattern) {
  std::string hex;
  while (hex.size() < 64)
    hex += pattern;
  hex.resize(64);
  return "sha256:" + hex;
}

TEST(AnchorProjection, KeepsTheLowBitsOfEachBigEndianWord) {
  // Word i of the digest is hex digits 8i..8i+7; the projection keeps
  // that word's low bits and nothing else.
  auto elements = anchorProjection(
      "sha256:ffffffff0000000012345678abcdef00"
      "00000000ffffffff87654321fedcba98");
  ASSERT_TRUE(static_cast<bool>(elements));
  constexpr uint32_t kMask = (1u << kAnchorProjectionBits) - 1;
  EXPECT_EQ((*elements)[0], 0xffffffffu & kMask);
  EXPECT_EQ((*elements)[1], 0x00000000u & kMask);
  EXPECT_EQ((*elements)[2], 0x12345678u & kMask);
  EXPECT_EQ((*elements)[3], 0xabcdef00u & kMask);
  EXPECT_EQ((*elements)[7], 0xfedcba98u & kMask);
}

TEST(AnchorProjection, EveryElementIsCanonicalForABabyBearWord) {
  // The property the definition exists for: no element can be reduced
  // on its way into a sponge, for any anchor at all. BabyBear is the
  // smallest characteristic a digest class frames here.
  constexpr uint32_t kBabyBear = 2013265921;
  for (llvm::StringRef pattern :
       {"f", "0", "9c", "ab", "7f", "80", "ff00", "0f1e2d3c"}) {
    auto elements = anchorProjection(anchorOf(pattern));
    ASSERT_TRUE(static_cast<bool>(elements)) << pattern.str();
    ASSERT_EQ(elements->size(), kAnchorProjectionElements);
    for (uint32_t element : *elements) {
      EXPECT_LT(element, 1u << kAnchorProjectionBits);
      EXPECT_LT(element, kBabyBear);
    }
  }
}

TEST(AnchorProjection, PacksElementsAtTheDigestClassLimbStride) {
  // The packed value and the elements a sponge receives must be the
  // same eight numbers, which holds only if the packing stride is the
  // class's own.
  std::string anchor = anchorOf("3c5a");
  auto elements = anchorProjection(anchor);
  auto value = anchorProjectionValue(anchor);
  ASSERT_TRUE(static_cast<bool>(elements));
  ASSERT_TRUE(static_cast<bool>(value));
  llvm::APInt packed(kAnchorProjectionElements * 32, *value, 10);
  for (unsigned index = 0; index < kAnchorProjectionElements; ++index)
    EXPECT_EQ(packed.extractBitsAsZExtValue(32, index * 32),
              (*elements)[index])
        << "limb " << index;
}

TEST(AnchorProjection, IsAFunctionOfTheAnchorAlone) {
  std::string anchor = anchorOf("2b7e");
  auto first = anchorProjectionValue(anchor);
  auto second = anchorProjectionValue(anchor);
  ASSERT_TRUE(static_cast<bool>(first));
  ASSERT_TRUE(static_cast<bool>(second));
  EXPECT_EQ(*first, *second);
}

TEST(AnchorProjection, DistinctAnchorsThatDifferInKeptBitsProjectApart) {
  auto low = anchorProjectionValue(
      "sha256:00000001000000000000000000000000"
      "00000000000000000000000000000000");
  auto other = anchorProjectionValue(
      "sha256:00000002000000000000000000000000"
      "00000000000000000000000000000000");
  ASSERT_TRUE(static_cast<bool>(low));
  ASSERT_TRUE(static_cast<bool>(other));
  EXPECT_NE(*low, *other);
}

TEST(AnchorProjection, RefusesAnythingThatIsNotAnAnchor) {
  const std::vector<std::string> refused = {
      "",
      "sha256:",
      "sha256:abc",
      "blake3:" + std::string(64, 'a'),
      std::string(64, 'a'),
      "sha256:" + std::string(63, 'a'),
      "sha256:" + std::string(65, 'a'),
      "sha256:" + std::string(64, 'A'),
      "sha256:" + std::string(64, 'g')};
  for (const std::string &bad : refused) {
    auto elements = anchorProjection(bad);
    EXPECT_FALSE(static_cast<bool>(elements)) << "admitted: " << bad;
    if (!elements)
      llvm::consumeError(elements.takeError());
    auto value = anchorProjectionValue(bad);
    EXPECT_FALSE(static_cast<bool>(value)) << "admitted: " << bad;
    if (!value)
      llvm::consumeError(value.takeError());
  }
}

} // namespace
