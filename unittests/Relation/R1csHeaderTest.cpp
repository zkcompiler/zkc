//===- R1csHeaderTest.cpp - The relation-artifact header reader -*- C++ -*-===//
// docs/spec/relations.md §5. This is the one place zkc reads bytes it
// did not produce, so what is tested is that it refuses everything the
// specification says it refuses, and that it cannot be walked off its
// own buffer by any prefix of a well-formed file.
//===----------------------------------------------------------------------===//

#include "zkc/Relation/R1csHeader.h"

#include "llvm/Support/Error.h"
#include "gtest/gtest.h"

#include <string>
#include <vector>

using namespace zkc::relation;

namespace {

/// The pinned field this repository's r1cs fixtures use.
constexpr llvm::StringLiteral kFieldOrder = "2305843009213697249";

void appendLittleEndian(std::string &out, uint64_t value, unsigned bytes) {
  for (unsigned index = 0; index < bytes; ++index)
    out.push_back(index < sizeof(uint64_t)
                      ? static_cast<char>((value >> (8 * index)) & 0xff)
                      : '\0');
}

struct HeaderFields {
  uint32_t fieldSize = 8;
  uint64_t prime = 2305843009213697249u;
  uint32_t wires = 8, publicOutputs = 0, publicInputs = 2, privateInputs = 5;
  uint64_t labels = 8;
  uint32_t constraints = 8;
};

std::string headerBody(const HeaderFields &fields) {
  std::string body;
  appendLittleEndian(body, fields.fieldSize, 4);
  appendLittleEndian(body, fields.prime, fields.fieldSize);
  appendLittleEndian(body, fields.wires, 4);
  appendLittleEndian(body, fields.publicOutputs, 4);
  appendLittleEndian(body, fields.publicInputs, 4);
  appendLittleEndian(body, fields.privateInputs, 4);
  appendLittleEndian(body, fields.labels, 8);
  appendLittleEndian(body, fields.constraints, 4);
  return body;
}

/// A whole file from its sections, so a test states only what it varies.
std::string fileOf(const std::vector<std::pair<uint32_t, std::string>> &sections,
                   llvm::StringRef magic = "r1cs", uint32_t version = 1,
                   std::optional<uint32_t> declaredCount = std::nullopt) {
  std::string out(magic);
  appendLittleEndian(out, version, 4);
  appendLittleEndian(out, declaredCount.value_or(sections.size()), 4);
  for (const auto &[type, payload] : sections) {
    appendLittleEndian(out, type, 4);
    appendLittleEndian(out, payload.size(), 8);
    out += payload;
  }
  return out;
}

std::string wellFormed(const HeaderFields &fields = {}) {
  return fileOf({{0x01, headerBody(fields)}, {0x02, std::string(4, '\0')}});
}

/// The refusal's text, for a case that must refuse.
std::string refusalOf(llvm::StringRef bytes,
                      llvm::StringRef field = kFieldOrder) {
  auto parsed = readR1csHeader(bytes, field);
  if (parsed) {
    ADD_FAILURE() << "admitted a file that must refuse";
    return {};
  }
  return llvm::toString(parsed.takeError());
}

TEST(R1csHeader, ReadsTheShapeAWellFormedFileStates) {
  auto parsed = readR1csHeader(wellFormed(), kFieldOrder);
  ASSERT_TRUE(static_cast<bool>(parsed)) << llvm::toString(parsed.takeError());
  EXPECT_EQ(parsed->prime, kFieldOrder.str());
  EXPECT_EQ(parsed->publicArity, 2);
  EXPECT_EQ(parsed->privateInputs, 5);
  EXPECT_EQ(parsed->constraintCount, 8);
  EXPECT_EQ(parsed->wires, 8);
}

TEST(R1csHeader, PublicArityCountsOutputsAndInputsTogether) {
  HeaderFields fields;
  fields.publicOutputs = 3;
  fields.publicInputs = 4;
  fields.wires = 32;
  auto parsed = readR1csHeader(wellFormed(fields), kFieldOrder);
  ASSERT_TRUE(static_cast<bool>(parsed));
  EXPECT_EQ(parsed->publicArity, 7);
}

TEST(R1csHeader, RefusesEveryRuleTheFormatProfileStates) {
  EXPECT_NE(refusalOf(fileOf({{0x01, headerBody({})}}, "r1sc")).find("magic"),
            std::string::npos);
  EXPECT_NE(refusalOf(fileOf({{0x01, headerBody({})}}, "r1cs", 2))
                .find("version"),
            std::string::npos);
  EXPECT_NE(refusalOf(fileOf({{0x01, headerBody({})}, {0x06, "\0\0\0\0"}}))
                .find("unadmitted"),
            std::string::npos);
  EXPECT_NE(refusalOf(fileOf({{0x01, headerBody({})}, {0x01, headerBody({})}}))
                .find("two header"),
            std::string::npos);
  EXPECT_NE(refusalOf(fileOf({{0x02, std::string(4, '\0')}})).find("no header"),
            std::string::npos);
  EXPECT_NE(refusalOf(fileOf({{0x01, headerBody({})}}, "r1cs", 1, 9))
                .find("sections"),
            std::string::npos);
  EXPECT_NE(refusalOf(fileOf({{0x01, headerBody({}) + std::string(1, '\0')}}))
                .find("trailing"),
            std::string::npos);
  HeaderFields narrow;
  narrow.wires = 3;
  EXPECT_NE(refusalOf(wellFormed(narrow)).find("wire count"),
            std::string::npos);
}

TEST(R1csHeader, RefusesAFieldSizeTheDeclaredFieldCannotHold) {
  HeaderFields wide;
  wide.fieldSize = 64;
  refusalOf(wellFormed(wide));
  // A field size that is not a whole number of bytes is refused whatever
  // the declared field: the format states its prime in whole bytes.
  HeaderFields ragged;
  ragged.fieldSize = 9;
  refusalOf(wellFormed(ragged));
}

TEST(R1csHeader, NoPrefixOfAWellFormedFileWalksOffTheBuffer) {
  // The cursor's whole job. Every truncation must refuse rather than
  // read past the end, and the reader is total on every input.
  std::string whole = wellFormed();
  for (size_t length = 0; length < whole.size(); ++length) {
    auto parsed = readR1csHeader(llvm::StringRef(whole).take_front(length),
                                 kFieldOrder);
    EXPECT_FALSE(static_cast<bool>(parsed))
        << "admitted a " << length << "-byte prefix";
    if (!parsed)
      llvm::consumeError(parsed.takeError());
  }
}

TEST(R1csHeader, IsTotalOnBytesThatAreNotAnR1csFileAtAll) {
  for (llvm::StringRef bytes :
       {llvm::StringRef(""), llvm::StringRef("r"), llvm::StringRef("r1cs"),
        llvm::StringRef("\xff\xff\xff\xff\xff\xff\xff\xff")}) {
    auto parsed = readR1csHeader(bytes, kFieldOrder);
    EXPECT_FALSE(static_cast<bool>(parsed));
    if (!parsed)
      llvm::consumeError(parsed.takeError());
  }
}

TEST(R1csHeader, AnUnboundedDeclaredFieldStillBoundsTheRead) {
  // A contract whose instance encoding names no field leaves the reader
  // its own bound rather than none.
  HeaderFields wide;
  wide.fieldSize = 4096;
  refusalOf(wellFormed(wide), "");
}

} // namespace
