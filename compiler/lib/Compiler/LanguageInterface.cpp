#include "zkc/Compiler/Language.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/JSON.h"
#include <set>

using namespace llvm;
namespace zkc::language {
namespace {
// LLVM JSON replaces duplicate object members. Reject them before parsing so a
// second spelling cannot silently replace an identity-bearing field.
Error preflight(StringRef bytes) {
  if (!json::isUTF8(bytes))
    return error("source.interface", "interface is not UTF-8");
  std::vector<std::optional<std::set<std::string>>> stack;
  for (size_t i = 0; i < bytes.size();) {
    char c = bytes[i++];
    if (c == '{' || c == '[') {
      if (stack.size() == 16)
        return error("source.limit", "interface nesting limit exceeded");
      stack.push_back(c == '{'
                          ? std::optional<std::set<std::string>>(std::in_place)
                          : std::nullopt);
    } else if (c == '}' || c == ']') {
      if (stack.empty() || bool(stack.back()) != (c == '}'))
        return error("source.interface", "unbalanced interface JSON");
      stack.pop_back();
    } else if (c == '"') {
      size_t start = i - 1;
      while (i < bytes.size() && bytes[i] != '"') {
        if (bytes[i] == '\\')
          ++i;
        ++i;
      }
      if (i >= bytes.size() || i - start > 4096)
        return error("source.interface",
                     "invalid or oversized interface string");
      StringRef spelling = bytes.slice(start, ++i);
      if (!validStringEncoding(spelling))
        return error("source.interface", "invalid interface string encoding");
      size_t next = i;
      while (next < bytes.size() && isSpace(bytes[next]))
        ++next;
      if (next < bytes.size() && bytes[next] == ':') {
        if (stack.empty() || !stack.back())
          return error("source.interface", "object key outside object");
        auto parsed = json::parse(spelling);
        if (!parsed)
          return parsed.takeError();
        auto key = parsed->getAsString();
        if (!key || !stack.back()->insert(key->str()).second)
          return error("source.interface", "duplicate interface key");
      }
    } else if (isDigit(c) || c == '-') {
      size_t start = i - 1;
      while (i < bytes.size() &&
             (isAlnum(bytes[i]) || StringRef(".+-").contains(bytes[i])))
        ++i;
      if (i - start > 20)
        return error("source.interface", "oversized interface number");
    }
  }
  return Error::success();
}
} // namespace
Error checkInterface(const CheckedOriginal &original, StringRef bytes,
                     const Limits &limits) {
  if (auto error = checkLimits(limits))
    return error;
  if (bytes.size() > limits.interfaceBytes)
    return error("source.limit", "interface byte limit exceeded");
  if (auto error = preflight(bytes))
    return error;
  auto actual = json::parse(bytes);
  if (!actual) {
    consumeError(actual.takeError());
    return error("source.interface", "invalid interface JSON");
  }
  auto expected = json::parse(original.interfaceJson());
  if (!expected)
    return expected.takeError();
  if (*actual != *expected)
    return error(
        "source.interface",
        "interface does not match the retained original and selected Entry");
  return Error::success();
}
} // namespace zkc::language
