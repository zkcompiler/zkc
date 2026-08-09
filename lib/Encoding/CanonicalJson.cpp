//===- CanonicalJson.cpp - Deterministic JSON emission ----------*- C++ -*-===//
#include "zkc/Encoding/CanonicalJson.h"

#include "zkc/Encoding/EncodingDomain.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/SHA256.h"

using namespace llvm;

namespace {

/// A second, deliberately small walk over already-valid JSON. It records the
/// decoded keys local to each object, so `"x"` and `"\u0078"` collide just as
/// they do in the parsed object. Value syntax stays LLVM's responsibility.
class UniqueKeyScanner {
public:
  explicit UniqueKeyScanner(StringRef input)
      : cursor(input.begin()), end(input.end()) {}

  Error scan() {
    if (Error error = scanValue())
      return error;
    skipWhitespace();
    if (cursor != end)
      return createStringError("duplicate-key scan did not consume the JSON");
    return Error::success();
  }

private:
  void skipWhitespace() {
    while (cursor != end && (*cursor == ' ' || *cursor == '\r' ||
                             *cursor == '\n' || *cursor == '\t'))
      ++cursor;
  }

  Expected<std::string> scanString() {
    if (cursor == end || *cursor != '"')
      return createStringError("duplicate-key scan expected a string");
    const char *start = cursor++;
    while (cursor != end) {
      char byte = *cursor++;
      if (byte == '\\') {
        if (cursor == end)
          break;
        ++cursor;
        continue;
      }
      if (byte != '"')
        continue;
      auto parsed = json::parse(StringRef(start, cursor - start));
      if (!parsed || !parsed->getAsString()) {
        if (!parsed)
          consumeError(parsed.takeError());
        return createStringError("duplicate-key scan found an invalid string");
      }
      return parsed->getAsString()->str();
    }
    return createStringError("duplicate-key scan found an unterminated string");
  }

  Error scanObject() {
    ++cursor; // '{'
    skipWhitespace();
    if (cursor != end && *cursor == '}') {
      ++cursor;
      return Error::success();
    }
    StringSet<> keys;
    while (cursor != end) {
      auto key = scanString();
      if (!key)
        return key.takeError();
      if (!keys.insert(*key).second)
        return createStringError("duplicate JSON object key '" + *key + "'");
      skipWhitespace();
      if (cursor == end || *cursor++ != ':')
        return createStringError("duplicate-key scan expected ':'");
      if (Error error = scanValue())
        return error;
      skipWhitespace();
      if (cursor != end && *cursor == ',') {
        ++cursor;
        skipWhitespace();
        continue;
      }
      if (cursor != end && *cursor == '}') {
        ++cursor;
        return Error::success();
      }
      return createStringError("duplicate-key scan expected ',' or '}'");
    }
    return createStringError("duplicate-key scan found an unterminated object");
  }

  Error scanArray() {
    ++cursor; // '['
    skipWhitespace();
    if (cursor != end && *cursor == ']') {
      ++cursor;
      return Error::success();
    }
    while (cursor != end) {
      if (Error error = scanValue())
        return error;
      skipWhitespace();
      if (cursor != end && *cursor == ',') {
        ++cursor;
        skipWhitespace();
        continue;
      }
      if (cursor != end && *cursor == ']') {
        ++cursor;
        return Error::success();
      }
      return createStringError("duplicate-key scan expected ',' or ']'");
    }
    return createStringError("duplicate-key scan found an unterminated array");
  }

  Error scanValue() {
    skipWhitespace();
    if (cursor == end)
      return createStringError("duplicate-key scan expected a value");
    if (*cursor == '{')
      return scanObject();
    if (*cursor == '[')
      return scanArray();
    if (*cursor == '"') {
      auto value = scanString();
      return value ? Error::success() : value.takeError();
    }
    while (cursor != end && *cursor != ',' && *cursor != ']' &&
           *cursor != '}' && *cursor != ' ' && *cursor != '\r' &&
           *cursor != '\n' && *cursor != '\t')
      ++cursor;
    return Error::success();
  }

  const char *cursor;
  const char *end;
};

} // namespace

Expected<json::Value> zkc::encoding::parseJsonUniqueKeys(StringRef input) {
  auto parsed = json::parse(input);
  if (!parsed)
    return parsed.takeError();
  UniqueKeyScanner scanner(input);
  if (Error error = scanner.scan())
    return std::move(error);
  return std::move(*parsed);
}

/// Writes one string literal over the enforced encoding domain
/// (kernel.md §3, item 4): printable ASCII only. The only escapes JSON then
/// requires are `"` and `\`; every other byte is emitted verbatim and
/// everything outside 0x20..0x7E is an error, never an escape. The two
/// implementations agree byte for byte because the interesting escaper
/// cases are unrepresentable, not hand-matched — the domain, not the
/// escaper, is the parity argument.
static Error writeString(StringRef str, raw_ostream &os) {
  os << '"';
  for (unsigned char byte : str.bytes()) {
    if (byte < 0x20 || byte > 0x7e)
      return createStringError(
          "string leaves the canonical encoding domain (printable ASCII)");
    if (byte == '"' || byte == '\\')
      os << '\\';
    os << static_cast<char>(byte);
  }
  os << '"';
  return Error::success();
}

llvm::Error zkc::encoding::writeCanonicalJson(const json::Value &value,
                                              raw_ostream &os) {
  switch (value.kind()) {
  case json::Value::Null:
    os << "null";
    return Error::success();
  case json::Value::Boolean:
    os << (*value.getAsBoolean() ? "true" : "false");
    return Error::success();
  case json::Value::Number: {
    std::optional<int64_t> integer = value.getAsInteger();
    if (!integer)
      return createStringError(
          "non-integer number cannot enter a canonical encoding");
    os << *integer;
    return Error::success();
  }
  case json::Value::String:
    return writeString(*value.getAsString(), os);
  case json::Value::Array: {
    os << '[';
    bool first = true;
    for (const json::Value &element : *value.getAsArray()) {
      if (!first)
        os << ',';
      first = false;
      if (Error err = writeCanonicalJson(element, os))
        return err;
    }
    os << ']';
    return Error::success();
  }
  case json::Value::Object: {
    const json::Object &object = *value.getAsObject();
    SmallVector<StringRef> keys;
    keys.reserve(object.size());
    for (const auto &entry : object)
      keys.push_back(StringRef(entry.first));
    // Keys are printable ASCII (writeString rejects anything else), so
    // byte-wise order is code-point order, which is how the reference
    // encoder sorts keys.
    llvm::sort(keys);
    os << '{';
    bool first = true;
    for (StringRef key : keys) {
      if (!first)
        os << ',';
      first = false;
      if (Error err = writeString(key, os))
        return err;
      os << ':';
      if (Error err = writeCanonicalJson(*object.get(key), os))
        return err;
    }
    os << '}';
    return Error::success();
  }
  }
  llvm_unreachable("unknown JSON value kind");
}

llvm::Expected<json::Value>
zkc::encoding::attributeToCanonicalJson(mlir::Attribute attribute,
                                        unsigned depth) {
  if (depth > kMaxAttrDepth)
    return createStringError(
        "attribute nesting exceeds the canonical depth bound");
  if (auto string = mlir::dyn_cast<mlir::StringAttr>(attribute)) {
    if (!inEncodingDomain(string.getValue()))
      return createStringError(
          "string leaves the canonical encoding domain (printable ASCII)");
    return json::Value(string.getValue().str());
  }
  if (mlir::isa<mlir::BoolAttr>(attribute))
    return createStringError(
        "boolean leaves the canonical encoding domain (no boolean encoding)");
  if (auto integer = mlir::dyn_cast<mlir::IntegerAttr>(attribute)) {
    const bool isUnsigned = integer.getType().isUnsignedInteger();
    if (!inIntegerDomain(integer.getValue(), isUnsigned))
      return createStringError(
          "integer leaves the canonical encoding domain (signed 64-bit)");
    return json::Value(
        isUnsigned ? static_cast<int64_t>(integer.getValue().getZExtValue())
                   : integer.getValue().getSExtValue());
  }
  if (auto array = mlir::dyn_cast<mlir::ArrayAttr>(attribute)) {
    json::Array result;
    for (mlir::Attribute member : array) {
      auto converted = attributeToCanonicalJson(member, depth + 1);
      if (!converted)
        return converted.takeError();
      result.push_back(std::move(*converted));
    }
    return json::Value(std::move(result));
  }
  if (auto dictionary = mlir::dyn_cast<mlir::DictionaryAttr>(attribute)) {
    json::Object result;
    for (mlir::NamedAttribute named : dictionary) {
      if (!inEncodingDomain(named.getName().getValue()))
        return createStringError(
            "dictionary key leaves the canonical encoding domain "
            "(printable ASCII)");
      auto converted = attributeToCanonicalJson(named.getValue(), depth + 1);
      if (!converted)
        return converted.takeError();
      result[named.getName().getValue()] = std::move(*converted);
    }
    return json::Value(std::move(result));
  }
  return createStringError("attribute kind has no canonical encoding");
}

llvm::Expected<std::string>
zkc::encoding::canonicalJsonBytes(const json::Value &value) {
  std::string bytes;
  raw_string_ostream stream(bytes);
  if (Error error = writeCanonicalJson(value, stream))
    return std::move(error);
  return bytes;
}

llvm::Expected<std::string>
zkc::encoding::taggedSha256Ref(StringRef domain, const json::Value &value) {
  auto bytes = canonicalJsonBytes(value);
  if (!bytes)
    return bytes.takeError();
  llvm::SHA256 hasher;
  hasher.update(domain);
  hasher.update(*bytes);
  return "sha256:" + llvm::toHex(hasher.final(), /*LowerCase=*/true);
}
