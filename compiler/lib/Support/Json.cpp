#include "zkc/Support/Json.h"
#include "zkc/Support/MLIRInput.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
namespace zkc {
json::Value naturalValue(StringRef digits) {
  return json::Object{{"natural", digits.str()}};
}
Expected<std::string> natural(const json::Value &value) {
  if (auto *object = value.getAsObject())
    if (object->size() == 1)
      if (auto digits = object->getString("natural"))
        if (!digits->empty() && digits->size() <= 1024 &&
            (digits->size() == 1 || digits->front() != '0') &&
            llvm::all_of(*digits, [](char c) { return c >= '0' && c <= '9'; }))
          return digits->str();
  return error("expected-natural");
}
// LLVM's JSON parser replaces unpaired surrogate escapes. Source labels must
// instead reject malformed Unicode, before any identity-relevant text is lost.
bool validStringEncoding(StringRef spelling) {
  if (!json::isUTF8(spelling))
    return false;
  for (size_t i = 1; i + 1 < spelling.size(); ++i) {
    if (spelling[i] != '\\')
      continue;
    if (spelling[++i] != 'u')
      continue;
    unsigned unit = 0;
    if (i + 4 >= spelling.size() ||
        spelling.substr(i + 1, 4).getAsInteger(16, unit))
      return false;
    i += 4;
    if (unit >= 0xdc00 && unit <= 0xdfff)
      return false;
    if (unit < 0xd800 || unit > 0xdbff)
      continue;
    if (i + 6 >= spelling.size() ||
        !spelling.substr(i + 1).starts_with("\\u") ||
        spelling.substr(i + 3, 4).getAsInteger(16, unit) || unit < 0xdc00 ||
        unit > 0xdfff)
      return false;
    i += 6;
  }
  return true;
}
namespace {
// LLVM accepts integral floats, leading signs/zeros and duplicate object keys.
// These formats must agree with typed JSON consumers. Check numeric spellings
// and surrogate escapes, and count authored keys. json::parse owns the
// remaining JSON grammar and decodes accepted strings.
std::optional<size_t> scanNaturalJsonKeys(StringRef text) {
  size_t keys = 0;
  for (size_t i = 0; i < text.size(); ++i) {
    if (text[i] == '"') {
      size_t start = i;
      while (++i < text.size() && text[i] != '"')
        if (text[i] == '\\' && i + 1 < text.size())
          ++i;
      if (i == text.size() || !validStringEncoding(text.slice(start, i + 1)))
        return std::nullopt;
      size_t next = i + 1;
      while (next < text.size() && isSpace(text[next]))
        ++next;
      if (next < text.size() && text[next] == ':')
        ++keys;
    } else if (text[i] == '-' || text[i] == '+' || text[i] == '.') {
      return std::nullopt;
    } else if (isDigit(text[i])) {
      if (text[i] == '0' && i + 1 < text.size() && isDigit(text[i + 1]))
        return std::nullopt;
      while (i + 1 < text.size() && isDigit(text[i + 1]))
        ++i;
      if (i + 1 < text.size() &&
          (text[i + 1] == '.' || text[i + 1] == 'e' || text[i + 1] == 'E'))
        return std::nullopt;
    }
  }
  return keys;
}
size_t countNaturalJsonKeys(const json::Value &value) {
  size_t keys = 0;
  if (auto *object = value.getAsObject()) {
    keys = object->size();
    for (auto &item : *object)
      keys += countNaturalJsonKeys(item.second);
  } else if (auto *array = value.getAsArray()) {
    for (auto &item : *array)
      keys += countNaturalJsonKeys(item);
  }
  return keys;
}
} // namespace
Expected<json::Value> parseNaturalJson(StringRef text, size_t byteLimit,
                                       unsigned depthLimit,
                                       StringRef invalidCode,
                                       StringRef limitCode) {
  if (text.size() > byteLimit || !mlirNestingWithinLimit(text, depthLimit))
    return error(limitCode);
  auto keys = scanNaturalJsonKeys(text);
  if (!keys)
    return error(invalidCode);
  auto parsed = json::parse(text);
  if (!parsed) {
    consumeError(parsed.takeError());
    return error(invalidCode);
  }
  // Any duplicate loses at least one authored key, including duplicate keys
  // spelled with distinct JSON escapes or containing a replaced object value.
  if (countNaturalJsonKeys(*parsed) != *keys)
    return error(invalidCode);
  return parsed;
}
Expected<json::Value> parseJson(StringRef text,
                                std::optional<size_t> *invalidStringOffset) {
  if (invalidStringOffset)
    invalidStringOffset->reset();
  if (text.size() > 1024 * 1024)
    return error("byte-limit");
  std::string translated;
  unsigned depth = 0;
  for (size_t i = 0; i < text.size();) {
    char ch = text[i];
    if (ch == '"') {
      size_t start = i++;
      bool closed = false;
      while (i < text.size()) {
        if (text[i] == '\\') {
          i += 2;
          continue;
        }
        if (text[i++] == '"') {
          closed = true;
          break;
        }
      }
      if (!closed || i > text.size())
        return error("invalid-json");
      if (!validStringEncoding(text.slice(start, i))) {
        if (invalidStringOffset)
          *invalidStringOffset = start;
        return error("invalid-json");
      }
      translated += text.slice(start, i).str();
    } else if (ch == '{' || ch == '}') {
      return error("invalid-shape");
    } else if (ch == '-' || (ch >= '0' && ch <= '9')) {
      bool negative = ch == '-';
      if (negative)
        ++i;
      size_t start = i;
      while (i < text.size() && text[i] >= '0' && text[i] <= '9')
        ++i;
      StringRef digits = text.slice(start, i);
      if (digits.empty() || (digits.size() > 1 && digits.front() == '0'))
        return error("invalid-json");
      if (digits.size() > 1024)
        return error("number-limit");
      if (i < text.size() &&
          (text[i] == '.' || text[i] == 'e' || text[i] == 'E'))
        return error("expected-natural");
      if (negative && digits != "0")
        return error("expected-natural");
      translated += "{\"natural\":\"" + digits.str() + "\"}";
    } else {
      if (ch == '[' && ++depth > 512)
        return error("depth-limit");
      if (ch == ']') {
        if (!depth)
          return error("invalid-json");
        --depth;
      }
      translated += ch;
      ++i;
    }
  }
  auto parsed = json::parse(translated);
  if (!parsed) {
    consumeError(parsed.takeError());
    return error("invalid-json");
  }
  return std::move(*parsed);
}
static void print(raw_ostream &out, const json::Value &value) {
  if (auto *array = value.getAsArray()) {
    out << '[';
    bool comma = false;
    for (auto &entry : *array) {
      if (comma)
        out << ',';
      comma = true;
      print(out, entry);
    }
    out << ']';
  } else if (value.getAsObject()) {
    auto digits = natural(value);
    if (digits)
      out << *digits;
    else {
      consumeError(digits.takeError());
      out << value;
    }
  } else
    out << value;
}
std::string printJson(const json::Value &value) {
  std::string text;
  raw_string_ostream out(text);
  print(out, value);
  return text;
}
} // namespace zkc
