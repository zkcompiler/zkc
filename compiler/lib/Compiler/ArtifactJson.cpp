#include "ArtifactJson.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
using namespace llvm;
namespace zkc::detail {
Expected<json::Value> parseArtifactJson(StringRef bytes) {
  if (bytes.size() > 16 * 1024 * 1024)
    return error("artifact-json-limit");
  unsigned depth = 0;
  size_t nodes = 0, keys = 0;
  for (size_t i = 0; i < bytes.size();) {
    char c = bytes[i];
    if (isSpace(c) || c == ',' || c == ':') {
      ++i;
      continue;
    }
    if (c == ']' || c == '}') {
      if (!depth)
        return error("artifact-json");
      --depth;
      ++i;
      continue;
    }
    if (++nodes > 250000)
      return error("artifact-json-limit");
    if (c == '"') {
      size_t start = i++;
      bool closed = false;
      while (i < bytes.size()) {
        if (bytes[i] == '\\') {
          i += 2;
          continue;
        }
        if (bytes[i++] == '"') {
          closed = true;
          break;
        }
      }
      if (!closed || i > bytes.size() ||
          !validStringEncoding(bytes.slice(start, i)))
        return error("artifact-json");
      size_t next = i;
      while (next < bytes.size() && isSpace(bytes[next]))
        ++next;
      keys += next < bytes.size() && bytes[next] == ':';
    } else if (c == '[' || c == '{') {
      if (++depth > 256)
        return error("artifact-json-limit");
      ++i;
    } else {
      size_t start = i++;
      while (i < bytes.size() && !isSpace(bytes[i]) && bytes[i] != ',' &&
             bytes[i] != ']' && bytes[i] != '}')
        ++i;
      auto token = bytes.slice(start, i);
      if (token == "true" || token == "false" || token == "null")
        continue;
      uint64_t number;
      if (token.empty() || (token.size() > 1 && token.front() == '0') ||
          !all_of(token, [](char digit) { return isDigit(digit); }) ||
          token.getAsInteger(10, number))
        return error("artifact-json");
    }
  }
  if (depth)
    return error("artifact-json");
  auto parsed = json::parse(bytes);
  if (!parsed) {
    consumeError(parsed.takeError());
    return error("artifact-json");
  }
  SmallVector<const json::Value *> pending{&*parsed};
  size_t decodedKeys = 0;
  while (!pending.empty()) {
    auto *value = pending.pop_back_val();
    if (auto *object = value->getAsObject()) {
      decodedKeys += object->size();
      for (auto &item : *object)
        pending.push_back(&item.second);
    } else if (auto *array = value->getAsArray())
      for (auto &item : *array)
        pending.push_back(&item);
  }
  if (keys != decodedKeys)
    return error("artifact-json");
  return std::move(*parsed);
}
} // namespace zkc::detail
