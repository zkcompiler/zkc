#include "zkc/Mathematical/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <algorithm>
#include <limits>

using namespace llvm;
namespace zkc::mathematical {
namespace {

Expected<uint64_t> naturalToken(StringRef spelling) {
  uint64_t value = 0;
  if (spelling.empty() || spelling.size() > 20 ||
      (spelling.size() > 1 && spelling.front() == '0'))
    return error("math-natural");
  for (char ch : spelling) {
    if (ch < '0' || ch > '9' ||
        value > (std::numeric_limits<uint64_t>::max() - (ch - '0')) / 10)
      return error("math-natural");
    value = value * 10 + (ch - '0');
  }
  return value;
}

// JSON syntax is small enough to validate before object construction. In
// particular, neither LLVM's last-key-wins behavior nor floating-point parsing
// is on this boundary. Strings reuse the existing strict Unicode check.
class TextReader {
  StringRef text;
  size_t offset = 0, nodes = 0;

  void whitespace() {
    while (offset < text.size() &&
           (text[offset] == ' ' || text[offset] == '\n' ||
            text[offset] == '\r' || text[offset] == '\t'))
      ++offset;
  }
  bool take(char ch) {
    whitespace();
    if (offset == text.size() || text[offset] != ch)
      return false;
    ++offset;
    return true;
  }
  Expected<std::string> string() {
    whitespace();
    size_t start = offset;
    if (offset == text.size() || text[offset++] != '"')
      return error("math-json");
    while (offset < text.size()) {
      char ch = text[offset++];
      if (ch == '\\') {
        if (offset == text.size())
          return error("math-json");
        ++offset;
      } else if (ch == '"') {
        auto token = text.slice(start, offset);
        if (!validStringEncoding(token))
          return error("math-unicode");
        auto parsed = json::parse(token);
        if (!parsed) {
          consumeError(parsed.takeError());
          return error("math-json");
        }
        return parsed->getAsString()->str();
      }
    }
    return error("math-json");
  }
  Expected<json::Value> value(unsigned depth) {
    if (depth > EncodingLimits::depth || ++nodes > EncodingLimits::nodes)
      return error("math-resource-limit");
    whitespace();
    if (offset == text.size())
      return error("math-json");
    char ch = text[offset];
    if (ch == '"') {
      auto result = string();
      if (!result)
        return result.takeError();
      return json::Value(std::move(*result));
    }
    if (ch == '[') {
      ++offset;
      json::Array result;
      if (take(']'))
        return json::Value(std::move(result));
      do {
        if (result.size() >= EncodingLimits::children - 1)
          return error("math-resource-limit");
        auto child = value(depth + 1);
        if (!child)
          return child.takeError();
        result.push_back(std::move(*child));
        if (take(']'))
          return json::Value(std::move(result));
      } while (take(','));
      return error("math-json");
    }
    if (ch == '{') {
      ++offset;
      json::Object result;
      if (take('}'))
        return json::Value(std::move(result));
      do {
        if (result.size() >= (EncodingLimits::children - 1) / 2)
          return error("math-resource-limit");
        auto key = string();
        if (!key)
          return key.takeError();
        if (result.get(*key))
          return error("math-duplicate-key");
        if (!take(':'))
          return error("math-json");
        auto child = value(depth + 1);
        if (!child)
          return child.takeError();
        result[*key] = std::move(*child);
        if (take('}'))
          return json::Value(std::move(result));
      } while (take(','));
      return error("math-json");
    }
    for (StringRef token : {"true", "false"})
      if (text.substr(offset).starts_with(token)) {
        offset += token.size();
        return json::Value(token == "true");
      }
    size_t start = offset;
    while (offset < text.size() && text[offset] >= '0' && text[offset] <= '9')
      ++offset;
    auto number = naturalToken(text.slice(start, offset));
    if (!number)
      return number.takeError();
    return json::Value(*number);
  }

public:
  explicit TextReader(StringRef text) : text(text) {}
  Expected<json::Value> read() {
    if (text.size() > EncodingLimits::jsonBytes)
      return error("math-resource-limit");
    auto result = value(0);
    if (!result)
      return result.takeError();
    whitespace();
    if (offset != text.size())
      return error("math-json-trailing");
    return result;
  }
};

struct TreeBudget {
  size_t nodes = 0, bytes = 0;
  Error charge(unsigned depth, size_t size) {
    if (depth > EncodingLimits::depth || ++nodes > EncodingLimits::nodes ||
        size > EncodingLimits::bytes - bytes)
      return error("math-resource-limit");
    bytes += size;
    return Error::success();
  }
};

class Encoder {
  TreeBudget budget;
  std::vector<uint8_t> output;

  void header(uint8_t tag, uint64_t count) {
    output.push_back(tag);
    for (unsigned i = 0; i != 8; ++i)
      output.push_back(count >> (i * 8));
  }
  Error string(StringRef text, unsigned depth) {
    if (text.size() > EncodingLimits::bytes || !json::isUTF8(text))
      return error("math-unicode");
    if (auto failure = budget.charge(depth, 9 + text.size()))
      return failure;
    header(0, text.size());
    output.insert(output.end(), text.bytes_begin(), text.bytes_end());
    return Error::success();
  }
  Error array(size_t size, unsigned depth) {
    if (size > EncodingLimits::children)
      return error("math-resource-limit");
    if (auto failure = budget.charge(depth, 9))
      return failure;
    header(1, size);
    return Error::success();
  }
  Error scalar(StringRef tag, StringRef payload, unsigned depth) {
    if (auto failure = array(2, depth))
      return failure;
    if (auto failure = string(tag, depth + 1))
      return failure;
    return string(payload, depth + 1);
  }
  Error value(const json::Value &input, unsigned depth) {
    if (auto boolean = input.getAsBoolean())
      return scalar("boolean", *boolean ? "true" : "false", depth);
    if (auto natural = input.getAsUINT64())
      return scalar("natural", std::to_string(*natural), depth);
    if (auto text = input.getAsString())
      return scalar("string", *text, depth);
    if (auto list = input.getAsArray()) {
      if (list->size() >= EncodingLimits::children)
        return error("math-resource-limit");
      if (auto failure = array(list->size() + 1, depth))
        return failure;
      if (auto failure = string("array", depth + 1))
        return failure;
      for (const auto &child : *list)
        if (auto failure = value(child, depth + 1))
          return failure;
      return Error::success();
    }
    if (auto object = input.getAsObject()) {
      if (object->size() > (EncodingLimits::children - 1) / 2)
        return error("math-resource-limit");
      if (auto failure = array(object->size() * 2 + 1, depth))
        return failure;
      if (auto failure = string("object", depth + 1))
        return failure;
      std::vector<StringRef> keys;
      keys.reserve(object->size());
      for (const auto &entry : *object)
        keys.push_back(entry.first);
      std::sort(keys.begin(), keys.end());
      for (StringRef key : keys) {
        if (auto failure = string(key, depth + 1))
          return failure;
        if (auto failure = value(*object->get(key), depth + 1))
          return failure;
      }
      return Error::success();
    }
    return error("math-value-kind");
  }

public:
  Expected<std::vector<uint8_t>> encode(const json::Value &input) {
    if (auto failure = value(input, 0))
      return failure;
    return std::move(output);
  }
};

class BinaryReader {
  ArrayRef<uint8_t> input;
  size_t offset = 0;
  TreeBudget budget;

  Expected<uint64_t> header(uint8_t tag, unsigned depth) {
    if (input.size() - offset < 9)
      return error("math-truncated");
    if (auto failure = budget.charge(depth, 9))
      return failure;
    if (input[offset++] != tag)
      return error("math-tree-tag");
    uint64_t count = 0;
    for (unsigned i = 0; i != 8; ++i)
      count |= uint64_t(input[offset++]) << (i * 8);
    return count;
  }
  Expected<StringRef> string(unsigned depth) {
    auto count = header(0, depth);
    if (!count)
      return count.takeError();
    if (*count > EncodingLimits::bytes - budget.bytes)
      return error("math-resource-limit");
    if (*count > input.size() - offset)
      return error("math-truncated");
    StringRef result(reinterpret_cast<const char *>(input.data() + offset),
                     *count);
    offset += *count;
    budget.bytes += *count;
    if (!json::isUTF8(result))
      return error("math-unicode");
    return result;
  }
  Expected<json::Value> value(unsigned depth) {
    auto count = header(1, depth);
    if (!count)
      return count.takeError();
    if (!*count || *count > EncodingLimits::children ||
        *count > EncodingLimits::nodes - budget.nodes ||
        *count > (input.size() - offset) / 9)
      return error("math-resource-limit");
    auto tag = string(depth + 1);
    if (!tag)
      return tag.takeError();
    if (*tag == "string" || *tag == "natural" || *tag == "boolean") {
      if (*count != 2)
        return error("math-tree-shape");
      auto payload = string(depth + 1);
      if (!payload)
        return payload.takeError();
      if (*tag == "string")
        return json::Value(payload->str());
      if (*tag == "boolean") {
        if (*payload != "true" && *payload != "false")
          return error("math-tree-shape");
        return json::Value(*payload == "true");
      }
      auto number = naturalToken(*payload);
      if (!number)
        return number.takeError();
      return json::Value(*number);
    }
    if (*tag == "array") {
      json::Array result;
      for (uint64_t i = 1; i < *count; ++i) {
        auto child = value(depth + 1);
        if (!child)
          return child.takeError();
        result.push_back(std::move(*child));
      }
      return json::Value(std::move(result));
    }
    if (*tag == "object" && *count % 2 == 1) {
      json::Object result;
      std::optional<StringRef> previous;
      for (uint64_t i = 1; i < *count; i += 2) {
        auto key = string(depth + 1);
        if (!key)
          return key.takeError();
        if (previous && *key <= *previous)
          return error("math-key-order");
        previous = *key;
        auto child = value(depth + 1);
        if (!child)
          return child.takeError();
        result[key->str()] = std::move(*child);
      }
      return json::Value(std::move(result));
    }
    return error("math-tree-shape");
  }

public:
  explicit BinaryReader(ArrayRef<uint8_t> input) : input(input) {}
  Expected<json::Value> read() {
    if (input.size() > EncodingLimits::bytes)
      return error("math-resource-limit");
    auto result = value(0);
    if (!result)
      return result.takeError();
    if (offset != input.size())
      return error("math-binary-trailing");
    return result;
  }
};
} // namespace

Expected<json::Value> parseValue(StringRef text) {
  auto result = TextReader(text).read();
  if (!result)
    return result.takeError();
  // The transport limit is separate; all converted-tree limits still apply.
  auto checked = encodeValue(*result);
  if (!checked)
    return checked.takeError();
  return result;
}
Expected<std::vector<uint8_t>> encodeValue(const json::Value &value) {
  return Encoder().encode(value);
}
Expected<json::Value> decodeValue(ArrayRef<uint8_t> bytes) {
  return BinaryReader(bytes).read();
}
Expected<std::string> subjectDigest(const json::Value &subject) {
  auto object = subject.getAsObject();
  if (!object || object->size() != 3 || !object->get("manifest") ||
      !object->get("module"))
    return error("math-envelope");
  auto profile = object->getString("profile");
  if (!profile ||
      (*profile != "zkc.math.v1" && *profile != "zkc.math.located.v1"))
    return error("math-profile");
  auto bytes = encodeValue(subject);
  if (!bytes)
    return bytes.takeError();
  SHA256 hash;
  hash.update(*profile == "zkc.math.v1" ? "zkc.math.subject.v1"
                                        : "zkc.math.located.v1");
  hash.update(StringRef("\0", 1));
  hash.update(*bytes);
  return toHex(hash.final(), true);
}
} // namespace zkc::mathematical
