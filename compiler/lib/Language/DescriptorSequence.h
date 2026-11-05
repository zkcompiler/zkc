#ifndef ZKC_LANGUAGE_DESCRIPTORSEQUENCE_H
#define ZKC_LANGUAGE_DESCRIPTORSEQUENCE_H
#include "Semantics.h"
#include <array>
#include <deque>
#include <limits>

namespace zkc::language::detail {
/// Inspect immutable closed storage without producing an expected descriptor.
/// Construction order is topological; sequence sharing never flattens entries.
bool checkClosedDescriptorStorage(Semantics &, const DescriptorShape &, Span,
                                  llvm::StringRef diagnosticCode);
/// Persistent ordered payload edges. Indices belong to this arena. Empty has
/// no node; branches never contain an empty child. Construction and traversal
/// use bounded explicit stacks, independently of authored expression depth.
class DescriptorSequence {
public:
  using Root = uint32_t;
  static constexpr Root empty = UINT32_MAX;
  using Node = DescriptorSequenceNode;
  DescriptorSequence(Semantics &types, std::deque<Node> &nodes)
      : types(types), nodes(nodes) {}
  std::optional<Root> singleton(unsigned, Span);
  std::optional<Root> concat(Root, Root, Span);
  std::optional<Root> replace(Root, uint64_t, unsigned, Span);
  std::optional<unsigned> at(Root, uint64_t, Span) const;
  uint64_t size(Root root) const {
    return root == empty ? 0 : nodes.at(root).length;
  }
  const std::deque<Node> &storage() const { return nodes; }

private:
  Semantics &types;
  std::deque<Node> &nodes;
  unsigned height(Root root) const {
    return root == empty ? 0 : nodes.at(root).height;
  }
  bool valid(Root root, Span) const;
  std::optional<Root> retain(const Node &, Span);
  std::optional<Root> branch(Root, Root, Span);
  std::optional<Root> balance(Root, Root, Span);
};
} // namespace zkc::language::detail
#endif
