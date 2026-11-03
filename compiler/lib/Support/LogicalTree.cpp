#include "zkc/Support/LogicalTree.h"
#include "zkc/Support/Refusal.h"
using namespace llvm;
namespace zkc {
namespace {
constexpr size_t maxBytes = 16 * 1024 * 1024;
constexpr unsigned maxDepth = 64;
constexpr unsigned maxNodes = 200000;
constexpr uint64_t maxElements = 32768;
// A tag byte and an eight-byte little-endian count begin every node.
constexpr size_t headerBytes = 9;

// The canonical byte length of `value` at `depth`. `nodes` counts the nodes of
// one encoding.
Expected<size_t> measure(const json::Value &value, unsigned depth,
                         unsigned &nodes) {
  if (depth > maxDepth || ++nodes > maxNodes)
    return error("logical-tree-limit");
  size_t size = headerBytes;
  if (auto string = value.getAsString()) {
    if (string->size() > maxBytes - headerBytes)
      return error("logical-tree-limit");
    size += string->size();
  } else if (auto *array = value.getAsArray()) {
    if (array->size() > maxElements)
      return error("logical-tree-limit");
    for (const auto &child : *array) {
      auto bytes = measure(child, depth + 1, nodes);
      if (!bytes)
        return bytes.takeError();
      if (*bytes > maxBytes - size)
        return error("logical-tree-limit");
      size += *bytes;
    }
  } else {
    return error("logical-tree-kind");
  }
  return size;
}
void header(std::string &out, unsigned tag, uint64_t count) {
  out.push_back(tag);
  for (unsigned i = 0; i < 8; ++i)
    out.push_back((count >> (8 * i)) & 255);
}
void write(std::string &out, const json::Value &value) {
  if (auto string = value.getAsString()) {
    header(out, 0, string->size());
    out.append(string->data(), string->size());
  } else {
    const auto &array = *value.getAsArray();
    header(out, 1, array.size());
    for (const auto &child : array)
      write(out, child);
  }
}
} // namespace
Expected<std::string> encodeLogicalTree(const json::Value &tree) {
  unsigned nodes = 0;
  auto size = measure(tree, 0, nodes);
  if (!size)
    return size.takeError();
  std::string out;
  out.reserve(*size);
  write(out, tree);
  return out;
}
Expected<std::string> encodeLogicalTreePrefix(const json::Array &elements,
                                              uint64_t arity) {
  if (arity > maxElements)
    return error("logical-tree-limit", "declared array arity");
  if (elements.size() > arity)
    return error("logical-tree-limit",
                 "prefix has more elements than its declared arity");
  // The array itself is the first node; its elements sit at depth one.
  unsigned nodes = 1;
  size_t size = headerBytes;
  for (const auto &element : elements) {
    auto bytes = measure(element, 1, nodes);
    if (!bytes)
      return bytes.takeError();
    if (*bytes > maxBytes - size)
      return error("logical-tree-limit");
    size += *bytes;
  }
  std::string out;
  out.reserve(size);
  header(out, 1, arity);
  for (const auto &element : elements)
    write(out, element);
  return out;
}
} // namespace zkc
