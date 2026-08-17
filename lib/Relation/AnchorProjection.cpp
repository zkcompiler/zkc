//===- AnchorProjection.cpp - An anchor's transcript projection -----------===//
// docs/spec/relations.md §2.8. The map is deliberately dull: keep the
// low bits of each digest word, which is what makes every element
// canonical for the field a digest class frames, and pack them the way
// the class already packs its limbs.
//===----------------------------------------------------------------------===//

#include "zkc/Relation/AnchorProjection.h"

#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/Error.h"

using namespace llvm;

namespace {
constexpr StringLiteral kPrefix = "sha256:";
constexpr unsigned kHexDigits = 64;
/// The digest class packs its limbs at a 32-bit stride, so the packed
/// value and the elements a sponge receives are the same eight numbers.
constexpr unsigned kLimbStride = 32;
} // namespace

Expected<std::vector<uint32_t>>
zkc::relation::anchorProjection(StringRef anchor) {
  if (!anchor.consume_front(kPrefix) || anchor.size() != kHexDigits)
    return createStringError(
        "an anchor projection needs a sha256:<64 lowercase hex> reference");
  std::vector<uint32_t> elements;
  elements.reserve(kAnchorProjectionElements);
  for (unsigned word = 0; word < kAnchorProjectionElements; ++word) {
    uint32_t value = 0;
    for (unsigned digit = 0; digit < 8; ++digit) {
      char c = anchor[word * 8 + digit];
      if (!llvm::isDigit(c) && !(c >= 'a' && c <= 'f'))
        return createStringError(
            "an anchor projection needs lowercase hexadecimal digits");
      value = (value << 4) | llvm::hexDigitValue(c);
    }
    elements.push_back(value & ((1u << kAnchorProjectionBits) - 1));
  }
  return elements;
}

Expected<std::string>
zkc::relation::anchorProjectionValue(StringRef anchor) {
  auto elements = anchorProjection(anchor);
  if (!elements)
    return elements.takeError();
  APInt packed(kAnchorProjectionElements * kLimbStride, 0);
  for (unsigned index = 0; index < elements->size(); ++index)
    packed.insertBits(APInt(kLimbStride, (*elements)[index]),
                      index * kLimbStride);
  SmallString<96> text;
  packed.toString(text, 10, /*Signed=*/false);
  return std::string(text);
}
