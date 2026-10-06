#include "zkc/Support/LogicalTree.h"
#include "zkc/Support/Refusal.h"
#include <cstdint>
using namespace llvm;
namespace zkc {
Expected<std::string> encodeLogicalTree(const json::Value &tree) {
  constexpr size_t maxBytes = 16 * 1024 * 1024;
  unsigned nodes = 0;
  auto measure = [&](auto &&self, const json::Value &v,
                     unsigned depth) -> Expected<size_t> {
    if (depth > 64 || ++nodes > 200000)
      return error("logical-tree-limit");
    size_t size = 9;
    if (auto s = v.getAsString()) {
      if (s->size() > maxBytes - 9)
        return error("logical-tree-limit");
      size += s->size();
    } else if (auto *a = v.getAsArray()) {
      if (a->size() > 32768)
        return error("logical-tree-limit");
      for (const auto &child : *a) {
        auto n = self(self, child, depth + 1);
        if (!n)
          return n.takeError();
        if (*n > maxBytes - size)
          return error("logical-tree-limit");
        size += *n;
      }
    } else
      return error("logical-tree-kind");
    return size;
  };
  auto size = measure(measure, tree, 0);
  if (!size)
    return size.takeError();
  std::string out;
  out.reserve(*size);
  auto header = [&](unsigned tag, uint64_t count) {
    out.push_back(tag);
    for (unsigned i = 0; i < 8; ++i)
      out.push_back((count >> (8 * i)) & 255);
  };
  auto write = [&](auto &&self, const json::Value &v) -> void {
    if (auto s = v.getAsString()) {
      header(0, s->size());
      out.append(s->data(), s->size());
    } else {
      const auto &a = *v.getAsArray();
      header(1, a.size());
      for (const auto &child : a)
        self(self, child);
    }
  };
  write(write, tree);
  return out;
}
} // namespace zkc
