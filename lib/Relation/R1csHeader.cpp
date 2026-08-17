//===- R1csHeader.cpp - The r1cs-bin-v1 reading form -----------*- C++ -*-===//
// The one place zkc reads relation-artifact bytes
// (docs/spec/relations.md §5). It reads a header and nothing else: the
// facts it establishes are the prime, the public arity, the private
// count, and the constraint count, and every other relation fact stays
// in the asserted tier no matter how well this reads.
//
// The format's own document says unknown section types must be ignored.
// This reader refuses them instead, because the reason it refuses the
// custom-gate sections — an unrecognized section can change what the
// sections a consumer does understand mean — generalizes to every type
// it does not know. Ignoring would be the lenient parse the loader
// discipline forbids.
//===----------------------------------------------------------------------===//

#include "zkc/Relation/R1csHeader.h"

#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallString.h"

using namespace llvm;
using namespace zkc::relation;

namespace {

/// A bounds-checked little-endian cursor. Every read states its own
/// extent, so a truncated file refuses at the read that ran off rather
/// than through an arithmetic wrap.
class Cursor {
public:
  Cursor(StringRef bytes) : bytes(bytes) {}

  bool remaining(uint64_t count) const {
    return count <= bytes.size() - at;
  }

  Expected<uint32_t> u32() {
    if (!remaining(4))
      return createStringError("truncated: a 32-bit field runs past the file");
    uint32_t value = 0;
    for (unsigned index = 0; index < 4; ++index)
      value |= static_cast<uint32_t>(
                   static_cast<unsigned char>(bytes[at + index]))
               << (8 * index);
    at += 4;
    return value;
  }

  Expected<uint64_t> u64() {
    if (!remaining(8))
      return createStringError("truncated: a 64-bit field runs past the file");
    uint64_t value = 0;
    for (unsigned index = 0; index < 8; ++index)
      value |= static_cast<uint64_t>(
                   static_cast<unsigned char>(bytes[at + index]))
               << (8 * index);
    at += 8;
    return value;
  }

  Expected<StringRef> take(uint64_t count) {
    if (!remaining(count))
      return createStringError("truncated: a section body runs past the file");
    StringRef slice = bytes.substr(at, count);
    at += count;
    return slice;
  }

  uint64_t offset() const { return at; }
  void seek(uint64_t position) { at = position; }
  uint64_t size() const { return bytes.size(); }

private:
  StringRef bytes;
  uint64_t at = 0;
};

/// The little-endian byte string as an exact decimal cardinality.
std::string decimalFromLittleEndian(StringRef bytes) {
  APInt value(static_cast<unsigned>(bytes.size() * 8 + 8), 0);
  for (size_t index = bytes.size(); index-- > 0;) {
    value <<= 8;
    value |= APInt(value.getBitWidth(),
                   static_cast<unsigned char>(bytes[index]));
  }
  SmallString<64> text;
  value.toString(text, 10, /*Signed=*/false);
  return std::string(text);
}

constexpr uint32_t kHeaderSection = 0x01;
constexpr uint32_t kConstraintSection = 0x02;
constexpr uint32_t kWireToLabelSection = 0x03;

} // namespace

Expected<R1csHeader>
zkc::relation::readR1csHeader(StringRef bytes, StringRef declaredFieldOrder) {
  Cursor cursor(bytes);
  auto magic = cursor.take(4);
  if (!magic)
    return magic.takeError();
  if (*magic != "r1cs")
    return createStringError("not an r1cs file: the magic bytes are not 'r1cs'");
  auto version = cursor.u32();
  if (!version)
    return version.takeError();
  if (*version != 1)
    return createStringError("r1cs version " + Twine(*version) +
                             " is not the admitted version 1");
  auto sectionCount = cursor.u32();
  if (!sectionCount)
    return sectionCount.takeError();

  // The format guarantees no section order, so sections are scanned by
  // type. Exactly one header is admitted: with two, a reader taking
  // either one silently prefers a declaration over its contradiction.
  std::optional<StringRef> headerBody;
  uint32_t seen = 0;
  while (cursor.offset() < cursor.size()) {
    auto type = cursor.u32();
    if (!type)
      return type.takeError();
    auto size = cursor.u64();
    if (!size)
      return size.takeError();
    auto body = cursor.take(*size);
    if (!body)
      return body.takeError();
    switch (*type) {
    case kHeaderSection:
      if (headerBody)
        return createStringError("two header sections: the file states its "
                                 "shape twice");
      headerBody = *body;
      break;
    case kConstraintSection:
    case kWireToLabelSection:
      // Admitted and deliberately unread; their extent was checked
      // above, which is all this reader claims about them.
      break;
    default:
      return createStringError(
          "unadmitted r1cs section type " + Twine(*type) +
          " (this reader admits the header, the constraints, and the "
          "wire-to-label map; an unrecognized section can change what "
          "the others mean)");
    }
    ++seen;
  }
  if (seen != *sectionCount)
    return createStringError("the file declares " + Twine(*sectionCount) +
                             " sections and carries " + Twine(seen));
  if (!headerBody)
    return createStringError("no header section: the file states no shape");

  Cursor header(*headerBody);
  auto fieldSize = header.u32();
  if (!fieldSize)
    return fieldSize.takeError();
  if (*fieldSize == 0 || *fieldSize % 8 != 0)
    return createStringError("'field_size' must be a positive multiple of 8");
  // Bounded before the prime is read: a crafted width would otherwise
  // ask for an allocation the refusal could no longer prevent. The
  // declared field order is the bound when the contract states one.
  uint64_t widthBound = 1024;
  if (!declaredFieldOrder.empty()) {
    APInt declared(static_cast<unsigned>(4 * declaredFieldOrder.size() + 8),
                   declaredFieldOrder, 10);
    widthBound = declared.getActiveBits() / 8 + 8;
  }
  if (*fieldSize > widthBound)
    return createStringError("'field_size' " + Twine(*fieldSize) +
                             " exceeds the width the declared field admits");
  auto prime = header.take(*fieldSize);
  if (!prime)
    return prime.takeError();

  R1csHeader parsed;
  parsed.prime = decimalFromLittleEndian(*prime);
  auto wires = header.u32();
  if (!wires)
    return wires.takeError();
  auto publicOutputs = header.u32();
  if (!publicOutputs)
    return publicOutputs.takeError();
  auto publicInputs = header.u32();
  if (!publicInputs)
    return publicInputs.takeError();
  auto privateInputs = header.u32();
  if (!privateInputs)
    return privateInputs.takeError();
  auto labels = header.u64();
  if (!labels)
    return labels.takeError();
  auto constraints = header.u32();
  if (!constraints)
    return constraints.takeError();
  if (header.offset() != header.size())
    return createStringError("the header section carries trailing bytes");

  parsed.wires = *wires;
  parsed.publicArity = static_cast<int64_t>(*publicOutputs) +
                       static_cast<int64_t>(*publicInputs);
  parsed.privateInputs = *privateInputs;
  parsed.constraintCount = *constraints;
  // Wire zero is the constant one, then the public outputs, the public
  // inputs, and the private inputs; a header whose counts do not fit
  // its own wire count is describing a different file.
  if (1 + parsed.publicArity + parsed.privateInputs > parsed.wires)
    return createStringError(
        "the header's own counts exceed its wire count: 1 + " +
        Twine(parsed.publicArity) + " + " + Twine(parsed.privateInputs) +
        " > " + Twine(parsed.wires));
  return parsed;
}
