#include "DescriptorSequence.h"
#include "DescriptorFactories.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
bool checkClosedDescriptorStorage(Semantics &types,
                                  const DescriptorShape &shape, Span span,
                                  StringRef diagnosticCode) {
  auto refuse = [&](StringRef message) {
    return types.fail(diagnosticCode, message, span);
  };
  if (!shape.arena)
    return refuse("closed descriptor has no arena");
  const auto &arena = *shape.arena;
  // Check the caller's cancellation before recursive contract inspection,
  // even when a smaller allowance would also refuse that inspection.
  if (!types.charge(2 * sizeof(std::vector<unsigned>) + 4 * sizeof(void *),
                    span))
    return false;
  // Every retained leaf must independently satisfy its installed signature,
  // including leaves outside the selected result. Port Types borrow the
  // immutable shape; collection inspection's owned result is prepaid here.
  for (unsigned i = 0; i < arena.leaves.size(); ++i) {
    const auto &leaf = arena.leaves[i];
    if (!types.chargeContract(leaf.contract, span) ||
        !types.charge(1 + leaf.operands.size() + leaf.children.size(), span))
      return false;
    if (leaf.factory || leaf.parameter || leaf.expression ||
        leaf.selectedView || !leaf.arguments.empty() ||
        !leaf.argumentOrder.empty())
      return refuse("closed leaf retains open authoring metadata");
    for (auto input : leaf.operands) {
      if (input.index >= shape.inputs.size())
        return refuse("closed leaf input is outside its signature");
      if (!types.chargeType(shape.inputs[input.index], span))
        return false;
    }
    for (const auto &child : leaf.children) {
      if (!types.chargeContract(child.contract, span))
        return false;
      if (child.node >= i ||
          child.contract != arena.leaves[child.node].contract)
        return refuse("closed leaf child is not a prior matching contract");
    }
    if (!finiteConstructorSignature(
            leaf.contract, leaf.kind, leaf.axis, leaf.operands.size(),
            [&](unsigned j) -> const Type & {
              return shape.inputs[leaf.operands[j].index];
            },
            leaf.children.size(),
            [&](unsigned j) -> const DescriptorContract & {
              return leaf.children[j].contract;
            }))
      return refuse("closed leaf differs from its installed constructor");
  }
  // Summarize each retained cell once, including historical roots. Contract
  // pointers borrow this immutable arena; no recursive Type owner is copied.
  if (arena.sequences.size() >
          UINT64_MAX / (sizeof(Type *) + sizeof(unsigned)) ||
      !types.charge(
          arena.sequences.size() * (sizeof(Type *) + sizeof(unsigned)), span))
    return types.diagnostic ? false : refuse("sequence storage size overflows");
  std::vector<const Type *> elements(arena.sequences.size());
  std::vector<unsigned> maximum(arena.sequences.size());
  for (unsigned i = 0; i < arena.sequences.size(); ++i) {
    const auto &node = arena.sequences[i];
    if (!types.charge(1 + node.count, span))
      return false;
    if (node.count) {
      if (node.count > node.elements.size() || node.length != node.count ||
          node.height != 1 || node.left != UINT32_MAX ||
          node.right != UINT32_MAX)
        return refuse("closed sequence chunk differs");
      for (unsigned j = 0; j < node.count; ++j) {
        auto child = node.elements[j];
        if (child >= arena.payloads.size())
          return refuse("closed sequence child is outside its arena");
        const auto &contract = descriptorType(arena.payloads[child].contract);
        if (!types.chargeType(contract, span))
          return false;
        if (elements[i] && *elements[i] != contract)
          return refuse("closed sequence has heterogeneous children");
        elements[i] = &contract;
        maximum[i] = std::max(maximum[i], child);
      }
    } else {
      if (node.left >= i || node.right >= i)
        return refuse("closed sequence branch is not topological");
      const auto &left = arena.sequences[node.left],
                 &right = arena.sequences[node.right];
      if (left.length > UINT64_MAX - right.length ||
          node.length != left.length + right.length ||
          node.height != std::max(left.height, right.height) + 1 ||
          left.height > right.height + 1 || right.height > left.height + 1)
        return refuse("closed sequence branch metadata differs");
      if (!types.chargeType(*elements[node.left], span))
        return false;
      if (*elements[node.left] != *elements[node.right])
        return refuse("closed sequence branch contracts differ");
      elements[i] = elements[node.left];
      maximum[i] = std::max(maximum[node.left], maximum[node.right]);
    }
  }
  for (unsigned i = 0; i < arena.payloads.size(); ++i) {
    const auto &payload = arena.payloads[i];
    const auto &contract = descriptorType(payload.contract);
    if (!types.chargeContract(payload.contract, span))
      return false;
    if (!payload.arguments.empty())
      return refuse("closed payload retains source statics");
    if (auto *leaf = std::get_if<unsigned>(&payload.value)) {
      if (!finiteDescriptorItem(payload.contract) ||
          *leaf >= arena.leaves.size() ||
          payload.contract != arena.leaves[*leaf].contract)
        return refuse("closed leaf contract differs");
    } else if (auto *children =
                   std::get_if<std::vector<unsigned>>(&payload.value)) {
      if (contract.kind != Type::Kind::DescriptorProduct ||
          children->size() != contract.arguments.size())
        return refuse("closed product arity differs");
      for (unsigned j = 0; j < children->size(); ++j)
        if ((*children)[j] >= i ||
            descriptorType(arena.payloads[(*children)[j]].contract) !=
                contract.arguments[j])
          return refuse("closed product child order or contract differs");
    } else if (auto *root = std::get_if<uint64_t>(&payload.value)) {
      if (contract.kind != Type::Kind::DescriptorSequence ||
          contract.arguments.empty() || contract.arguments.size() > 2 ||
          !isDescriptor(contract.arguments.front()) ||
          (*root != UINT32_MAX && *root >= arena.sequences.size()))
        return refuse("closed sequence contract or root differs");
      auto length = *root == UINT32_MAX ? 0 : arena.sequences[*root].length;
      if (contract.arguments.size() == 2 &&
          (contract.arguments[1].kind != Type::Kind::Natural ||
           !contract.arguments[1].dimension.isClosed() ||
           contract.arguments[1].dimension.closedValue() != length))
        return refuse("closed sequence exact extent differs");
      if (*root != UINT32_MAX &&
          (maximum[*root] >= i ||
           *elements[*root] != contract.arguments.front()))
        return refuse("closed sequence child order or contract differs");
    } else
      return refuse("closed payload retains a typed residual");
  }
  return true;
}
bool DescriptorSequence::valid(Root root, Span span) const {
  return root == empty || root < nodes.size() ||
         types.fail("source.descriptor-projection", "foreign sequence root",
                    span);
}
std::optional<DescriptorSequence::Root>
DescriptorSequence::retain(const Node &node, Span span) {
  // deque retains existing cells without moving them. Charge the cell, the
  // copied scratch cell, and a conservative allocation/map-pointer allowance
  // before the allocation. No historical sequence vector is copied.
  if (nodes.size() >= empty ||
      !types.charge(sizeof(Node) + 4 * sizeof(void *), span)) {
    if (!types.diagnostic)
      types.fail("source.limit", "sequence arena index exhausted", span);
    return {};
  }
  Root result = nodes.size();
  nodes.push_back(node);
  return result;
}
std::optional<DescriptorSequence::Root>
DescriptorSequence::singleton(unsigned element, Span span) {
  if (!types.charge(sizeof(Node), span))
    return {};
  Node node;
  node.length = node.count = 1;
  node.elements[0] = element;
  return retain(std::move(node), span);
}
std::optional<DescriptorSequence::Root>
DescriptorSequence::branch(Root left, Root right, Span span) {
  if (left == empty)
    return right;
  if (right == empty)
    return left;
  const auto &a = nodes[left], &b = nodes[right];
  if (a.length > UINT64_MAX - b.length) {
    types.fail("source.limit", "sequence length overflows uint64", span);
    return {};
  }
  if (!types.charge(sizeof(Node), span))
    return {};
  Node node;
  node.length = a.length + b.length;
  if (a.count && b.count && a.count + b.count <= node.elements.size()) {
    node.count = a.count + b.count;
    std::copy_n(a.elements.begin(), a.count, node.elements.begin());
    std::copy_n(b.elements.begin(), b.count, node.elements.begin() + a.count);
  } else {
    node.left = left;
    node.right = right;
    node.height = std::max(a.height, b.height) + 1;
  }
  return retain(std::move(node), span);
}
std::optional<DescriptorSequence::Root>
DescriptorSequence::balance(Root left, Root right, Span span) {
  if (!types.charge(1, span))
    return {};
  if (height(left) > height(right) + 1) {
    const auto &a = nodes[left];
    if (height(a.left) >= height(a.right)) {
      auto tail = branch(a.right, right, span);
      return tail ? branch(a.left, *tail, span) : std::nullopt;
    }
    const auto &middle = nodes[a.right];
    auto head = branch(a.left, middle.left, span);
    auto tail = head ? branch(middle.right, right, span) : std::nullopt;
    return tail ? branch(*head, *tail, span) : std::nullopt;
  }
  if (height(right) > height(left) + 1) {
    const auto &b = nodes[right];
    if (height(b.right) >= height(b.left)) {
      auto head = branch(left, b.left, span);
      return head ? branch(*head, b.right, span) : std::nullopt;
    }
    const auto &middle = nodes[b.left];
    auto head = branch(left, middle.left, span);
    auto tail = head ? branch(middle.right, b.right, span) : std::nullopt;
    return tail ? branch(*head, *tail, span) : std::nullopt;
  }
  return branch(left, right, span);
}
std::optional<DescriptorSequence::Root>
DescriptorSequence::concat(Root left, Root right, Span span) {
  if (!valid(left, span) || !valid(right, span))
    return {};
  if (size(left) > UINT64_MAX - size(right)) {
    types.fail("source.limit", "sequence length overflows uint64", span);
    return {};
  }
  struct Step {
    Root sibling;
    bool left;
  };
  // An AVL with uint64 length cannot exceed this height. Stack storage is
  // charged before use, including failed joins.
  std::array<Step, 96> path;
  if (!types.charge(sizeof(path), span))
    return {};
  unsigned depth = 0;
  while (height(left) > height(right) + 1 || height(right) > height(left) + 1) {
    if (!types.charge(1, span) || depth == path.size()) {
      if (!types.diagnostic)
        types.fail("source.limit", "sequence AVL path exhausted", span);
      return {};
    }
    if (height(left) > height(right) + 1) {
      const auto &node = nodes[left];
      path[depth++] = {node.left, true};
      left = node.right;
    } else {
      const auto &node = nodes[right];
      path[depth++] = {node.right, false};
      right = node.left;
    }
  }
  auto result = branch(left, right, span);
  while (result && depth) {
    auto step = path[--depth];
    result = step.left ? balance(step.sibling, *result, span)
                       : balance(*result, step.sibling, span);
  }
  return result;
}
std::optional<unsigned> DescriptorSequence::at(Root root, uint64_t index,
                                               Span span) const {
  if (!valid(root, span))
    return {};
  if (index >= size(root)) {
    types.fail("source.descriptor-projection", "sequence index is out of range",
               span);
    return {};
  }
  while (true) {
    if (!types.charge(1, span))
      return {};
    const auto &node = nodes[root];
    if (node.count)
      return node.elements[index];
    auto length = size(node.left);
    if (index < length)
      root = node.left;
    else {
      index -= length;
      root = node.right;
    }
  }
}
std::optional<DescriptorSequence::Root>
DescriptorSequence::replace(Root root, uint64_t index, unsigned element,
                            Span span) {
  if (!valid(root, span))
    return {};
  if (index >= size(root)) {
    types.fail("source.descriptor-projection",
               "sequence replacement is out of range", span);
    return {};
  }
  struct Step {
    Root sibling;
    bool left;
  };
  std::array<Step, 96> path;
  if (!types.charge(sizeof(path), span))
    return {};
  unsigned depth = 0;
  while (!nodes[root].count) {
    if (!types.charge(1, span) || depth == path.size()) {
      if (!types.diagnostic)
        types.fail("source.limit", "sequence AVL path exhausted", span);
      return {};
    }
    const auto &node = nodes[root];
    auto length = size(node.left);
    if (index < length) {
      path[depth++] = {node.right, false};
      root = node.left;
    } else {
      path[depth++] = {node.left, true};
      root = node.right;
      index -= length;
    }
  }
  if (!types.charge(sizeof(Node), span))
    return {};
  auto edited = nodes[root];
  edited.elements[index] = element;
  auto result = retain(std::move(edited), span);
  while (result && depth) {
    auto step = path[--depth];
    result = step.left ? branch(step.sibling, *result, span)
                       : branch(*result, step.sibling, span);
  }
  return result;
}
} // namespace zkc::language::detail
