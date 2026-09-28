#include "zkc/Mathematical/Codec.h"
#include "zkc/Mathematical/Raw.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace zkc::mathematical;

namespace {
template <class T> bool refused(Expected<T> result) {
  if (result)
    return false;
  consumeError(result.takeError());
  return true;
}
bool checkText(StringRef text) {
  auto value = parseValue(text);
  if (!value) {
    errs() << toString(value.takeError()) << '\n';
    return false;
  }
  auto bytes = encodeValue(*value);
  if (!bytes) {
    errs() << toString(bytes.takeError()) << '\n';
    return false;
  }
  auto decoded = decodeValue(*bytes);
  if (!decoded) {
    errs() << toString(decoded.takeError()) << '\n';
    return false;
  }
  if (*decoded != *value)
    return false;
  auto second = encodeValue(*decoded);
  if (!second) {
    consumeError(second.takeError());
    return false;
  }
  if (*second != *bytes)
    return false;
  // Every truncation refuses, including those inside a scalar length.
  for (size_t size = 0; size < bytes->size(); ++size)
    if (!refused(decodeValue(ArrayRef<uint8_t>(*bytes).take_front(size))))
      return false;
  bytes->push_back(0);
  return refused(decodeValue(*bytes));
}
} // namespace

int main(int argc, char **argv) {
  if (argc == 3) {
    // This test driver is also the native endpoint of independent-reader tests.
    auto file = MemoryBuffer::getFile(argv[2]);
    if (!file)
      return 2;
    StringRef input = (*file)->getBuffer();
    auto value = StringRef(argv[1]) == "binary"
                     ? decodeValue(ArrayRef<uint8_t>(
                           reinterpret_cast<const uint8_t *>(input.data()),
                           input.size()))
                     : parseValue(input);
    if (!value) {
      errs() << toString(value.takeError()) << '\n';
      return 1;
    }
    if (StringRef(argv[1]) == "schema") {
      auto subject = raw::decode(*value);
      if (!subject) {
        errs() << toString(subject.takeError()) << '\n';
        return 1;
      }
      auto encoded = raw::encode(*subject);
      if (!encoded) {
        errs() << toString(encoded.takeError()) << '\n';
        return 1;
      }
      if (*encoded != *value) {
        errs() << "raw schema roundtrip mismatch\n";
        return 1;
      }
    }
    auto bytes = encodeValue(*value);
    if (!bytes) {
      errs() << toString(bytes.takeError()) << '\n';
      return 1;
    }
    outs() << toHex(*bytes, true) << '\n';
    auto digest = subjectDigest(*value);
    if (digest)
      outs() << *digest << '\n';
    else
      consumeError(digest.takeError());
    return 0;
  }
  if (argc != 1)
    return 2;
  for (StringRef input :
       {R"({"a":[0,18446744073709551615,true,false,"\u0000"],"한글":"😀"})",
        "{}", "[]", "0", "false", R"("\ud83d\ude00")"})
    if (!checkText(input))
      return 1;
  for (StringRef input : {"",
                          "null",
                          "-0",
                          "-1",
                          "1.0",
                          "1e0",
                          "01",
                          "18446744073709551616",
                          R"({"a":0,"\u0061":1})",
                          R"({"a":1,"a":2})",
                          "[0,]",
                          "{,}",
                          "[true false]",
                          "true false",
                          R"("\ud800")",
                          R"("\udc00")",
                          "\"\xc0\xaf\"",
                          "\"\xed\xa0\x80\"",
                          "NaN",
                          "Infinity"})
    if (!refused(parseValue(input))) {
      errs() << "accepted malformed JSON: " << input << '\n';
      return 1;
    }
  for (json::Value input :
       {json::Value(nullptr), json::Value(-1), json::Value(1.0)})
    if (!refused(encodeValue(input)))
      return 1;
  // Root depth zero; scalar payload consumes one further tree level.
  std::string nested = "0";
  for (unsigned depth = 1; depth <= 64; ++depth) {
    nested = '[' + nested + ']';
    auto value = parseValue(nested);
    if (depth == 64) {
      if (!refused(std::move(value)))
        return 1;
    } else if (!value) {
      errs() << toString(value.takeError()) << '\n';
      return 1;
    }
  }
  json::Array maximum;
  for (size_t i = 0; i != EncodingLimits::children - 1; ++i)
    maximum.push_back(0);
  auto admitted = encodeValue(json::Value(json::Array(maximum)));
  if (!admitted) {
    errs() << toString(admitted.takeError());
    return 1;
  }
  maximum.push_back(0);
  if (!refused(encodeValue(json::Value(std::move(maximum)))))
    return 1;
  auto bytes = encodeValue(json::Value("hello"));
  if (!bytes) {
    consumeError(bytes.takeError());
    return 1;
  }
  // A forged huge child count must refuse before allocating that many values.
  for (size_t i = 1; i != 9; ++i)
    (*bytes)[i] = 255;
  if (!refused(decodeValue(*bytes)))
    return 1;
  outs() << "mathematical canonical values and malformed controls passed\n";
  return 0;
}
