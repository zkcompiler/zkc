//===- CanonicalJsonTest.cpp - The byte format parity rests on --*- C++ -*-===//
// Byte parity with the reference twin is the definition of done for
// encoding work, and every one of those diffs compares bytes this
// writer produced. Its determinism and its escaping are therefore
// properties of the whole parity argument rather than of one artifact,
// so they are stated here rather than inferred from a corpus.
//===----------------------------------------------------------------------===//

#include "zkc/Encoding/CanonicalJson.h"

#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"
#include "gtest/gtest.h"

#include <string>

using namespace zkc::encoding;
using namespace llvm;

namespace {

std::string canonical(const json::Value &value) {
  std::string out;
  raw_string_ostream stream(out);
  Error error = writeCanonicalJson(value, stream);
  EXPECT_FALSE(static_cast<bool>(error));
  if (error)
    consumeError(std::move(error));
  return out;
}

TEST(CanonicalJson, SortsObjectKeysAndHoldsArrayOrder) {
  json::Object object;
  object["zebra"] = 1;
  object["alpha"] = 2;
  object["middle"] = 3;
  EXPECT_EQ(canonical(json::Value(std::move(object))),
            "{\"alpha\":2,\"middle\":3,\"zebra\":1}");
  EXPECT_EQ(canonical(json::Array{3, 1, 2}), "[3,1,2]");
}

TEST(CanonicalJson, IsIndependentOfInsertionOrder) {
  json::Object first, second;
  for (StringRef key : {"b", "a", "d", "c"})
    first[key] = key.size();
  for (StringRef key : {"c", "d", "a", "b"})
    second[key] = key.size();
  EXPECT_EQ(canonical(json::Value(std::move(first))),
            canonical(json::Value(std::move(second))));
}

TEST(CanonicalJson, CarriesNoWhitespace) {
  json::Object nested;
  nested["inner"] = json::Array{1, json::Object{{"deep", "value"}}};
  std::string text = canonical(json::Value(std::move(nested)));
  EXPECT_EQ(text.find(' '), std::string::npos) << text;
  EXPECT_EQ(text.find('\n'), std::string::npos) << text;
}

TEST(CanonicalJson, EscapesExactlyTheTwoCharactersTheDomainAdmits) {
  // The encoding domain is printable ASCII, so a quotation mark and a
  // backslash are the only characters a string can hold that JSON must
  // escape. That is what makes the two writers agree byte for byte
  // without replicating an escaper.
  EXPECT_EQ(canonical(json::Value("plain")), "\"plain\"");
  EXPECT_EQ(canonical(json::Value("a\"b")), "\"a\\\"b\"");
  EXPECT_EQ(canonical(json::Value("a\\b")), "\"a\\\\b\"");
  EXPECT_EQ(canonical(json::Value("\"\\")), "\"\\\"\\\\\"");
  for (char c = 0x20; c > 0 && c <= 0x7e; ++c) {
    if (c == '"' || c == '\\')
      continue;
    std::string text(1, c);
    EXPECT_EQ(canonical(json::Value(text)), "\"" + text + "\"")
        << "character " << int(c);
  }
}

TEST(CanonicalJson, RoundTripsThroughItsOwnParser) {
  json::Object object;
  object["name"] = "a value with \" and \\";
  object["count"] = 42;
  object["nested"] = json::Object{{"b", json::Array{1, 2, 3}}, {"a", true}};
  std::string once = canonical(json::Value(std::move(object)));
  auto reparsed = parseJsonUniqueKeys(once);
  ASSERT_TRUE(static_cast<bool>(reparsed)) << once;
  EXPECT_EQ(canonical(*reparsed), once);
}

TEST(CanonicalJson, RefusesDuplicateKeysAtEveryDepth) {
  for (StringRef text :
       {"{\"a\":1,\"a\":2}", "{\"outer\":{\"a\":1,\"a\":2}}",
        "[{\"a\":1,\"a\":2}]", "{\"a\":1,\"b\":2,\"a\":3}"}) {
    auto parsed = parseJsonUniqueKeys(text);
    EXPECT_FALSE(static_cast<bool>(parsed)) << "admitted: " << text.str();
    if (!parsed)
      consumeError(parsed.takeError());
  }
}

TEST(CanonicalJson, AdmitsKeysThatOnlyLookAlike) {
  auto parsed = parseJsonUniqueKeys("{\"a\":1,\"A\":2,\"a \":3}");
  ASSERT_TRUE(static_cast<bool>(parsed));
  EXPECT_EQ(canonical(*parsed), "{\"A\":2,\"a\":1,\"a \":3}");
}

TEST(CanonicalJson, RefusesTextThatIsNotJson) {
  for (StringRef text : {"", "{", "{\"a\":}", "nope", "{\"a\":1,}"}) {
    auto parsed = parseJsonUniqueKeys(text);
    EXPECT_FALSE(static_cast<bool>(parsed)) << "admitted: " << text.str();
    if (!parsed)
      consumeError(parsed.takeError());
  }
}

} // namespace
