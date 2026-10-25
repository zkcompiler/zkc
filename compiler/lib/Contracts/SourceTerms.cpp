#include "zkc/Contracts/SourceTerms.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringSet.h"
#include <cstdlib>
#include <utf8proc.h>

using namespace llvm;
namespace zkc {
namespace {
bool text(const json::Value &value, size_t limit = 512) {
  auto s = value.getAsString();
  return s && !s->empty() && s->size() <= limit && json::isUTF8(*s) &&
         !s->contains('\0');
}
bool path(const json::Value &value, size_t limit = 512) {
  if (!text(value, limit))
    return false;
  auto s = *value.getAsString();
  utf8proc_uint8_t *normalized = nullptr;
  auto size = utf8proc_map(
      reinterpret_cast<const utf8proc_uint8_t *>(s.data()), s.size(),
      &normalized,
      static_cast<utf8proc_option_t>(UTF8PROC_STABLE | UTF8PROC_COMPOSE));
  bool nfc = size >= 0 &&
             StringRef(reinterpret_cast<const char *>(normalized), size) == s;
  utf8proc_free(normalized);
  if (!nfc)
    return false;
  SmallVector<StringRef> parts;
  s.split(parts, "::");
  return all_of(parts, [](StringRef part) {
    return !part.empty() && all_of(part, [](unsigned char c) {
      return c >= 128 || isAlnum(c) || c == '_';
    }) && !(part.front() >= '0' && part.front() <= '9');
  });
}
bool decimal(const json::Value &value) {
  auto s = value.getAsString();
  return text(value) && (s->size() == 1 || s->front() != '0') &&
         all_of(*s, [](char c) { return c >= '0' && c <= '9'; });
}
struct Reader {
  unsigned remaining = 4096;
  bool term(const json::Value &value, unsigned depth = 0) {
    if (!remaining || depth >= 64)
      return false;
    --remaining;
    auto a = value.getAsArray();
    if (!a || a->empty())
      return false;
    auto tag = (*a)[0].getAsString();
    if (!tag)
      return false;
    auto arguments = [&](unsigned index) {
      auto children = (*a)[index].getAsArray();
      return children && children->size() <= 512 &&
             children->size() <= remaining &&
             all_of(*children, [&](const json::Value &child) {
               return term(child, depth + 1);
             });
    };
    if (*tag == "nat")
      return a->size() == 2 && decimal((*a)[1]);
    if (*tag == "field" || *tag == "group")
      return a->size() == 2 && text((*a)[1]);
    if (*tag == "domain" || *tag == "asset")
      return a->size() == 3 && text((*a)[1]) && text((*a)[2]);
    if (*tag == "bool" || *tag == "index" || *tag == "unit")
      return a->size() == 1;
    if (*tag == "tuple")
      return a->size() == 2 && arguments(1);
    if (*tag == "array")
      return a->size() == 3 && term((*a)[1], depth + 1) && decimal((*a)[2]);
    if (*tag == "nominal") {
      auto kind = a->size() == 4 ? (*a)[1].getAsString() : std::nullopt;
      return kind &&
             (*kind == "record" || *kind == "variant" ||
              *kind == "associated" || *kind == "module") &&
             path((*a)[2]) && arguments(3);
    }
    if (*tag == "builtin" || *tag == "formal")
      return a->size() == 3 && text((*a)[1]) && arguments(2);
    return false;
  }
};
} // namespace
Error checkStaticTerm(const json::Value &value) {
  return Reader().term(value) ? Error::success() : error("source.static-term");
}
Error checkProtocolOrigin(const json::Value &value) {
  auto a = value.getAsArray();
  if (!a || a->size() != 2 || !path((*a)[0], 2048))
    return error("source.protocol-origin");
  auto bindings = (*a)[1].getAsArray();
  if (!bindings || bindings->size() > 128)
    return error("source.protocol-origin");
  Reader reader;
  StringSet<> names;
  for (const auto &binding : *bindings) {
    auto pair = binding.getAsArray();
    if (!pair || pair->size() != 2 || !path((*pair)[0]) ||
        pair->front().getAsString()->contains("::") ||
        !names.insert(*pair->front().getAsString()).second ||
        !reader.term((*pair)[1]))
      return error("source.protocol-origin");
  }
  return Error::success();
}
} // namespace zkc
