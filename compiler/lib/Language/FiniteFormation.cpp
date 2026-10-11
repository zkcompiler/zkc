#include "FiniteFormation.h"
using namespace llvm;
namespace zkc::language::detail {
bool checkFiniteFormation(Semantics &types, const FiniteComputation &finite,
                          const Type &result, bool total, Span span,
                          const FiniteFormationEvidence &evidence) {
  const auto &shape = *finite.domain;
  using Kind = DomainBinding::Kind;
  struct Cardinality {
    std::optional<ValueId> container;
    unsigned axis = 0;
    std::optional<uint64_t> fixed;
  };
  std::vector<Cardinality> cards;
  for (const auto &node : shape.nodes) {
    if (!types.charge(node.operands.size() + node.children.size() + 1, span))
      return false;
    Cardinality card;
    if (node.kind == Kind::Zip) {
      card = cards[node.children.front()];
    } else if (node.kind == Kind::Product) {
      card.fixed = 1;
      for (auto child : node.children) {
        auto n = cards[child].fixed;
        if (n && !*n) {
          card.fixed = 0;
          break;
        }
        if (!n || !card.fixed || (*n && *card.fixed > UINT64_MAX / *n))
          card.fixed.reset();
        else
          *card.fixed *= *n;
      }
    } else if (node.kind == Kind::Range) {
      auto lo = evidence.constant(node.operands[0]);
      auto hi = evidence.constant(node.operands[1]);
      if (lo && hi)
        card.fixed = *hi > *lo ? *hi - *lo : 0;
    } else if (node.kind == Kind::Elements || node.kind == Kind::SourceArray ||
               node.kind == Kind::Indices || node.kind == Kind::MatrixRow ||
               node.kind == Kind::MatrixColumn) {
      card.container = node.operands.front();
      card.axis = node.kind == Kind::Indices     ? node.axis
                  : node.kind == Kind::MatrixRow ? 1
                                                 : 0;
      card.fixed = evidence.extent(*card.container, card.axis);
    }
    cards.push_back(std::move(card));
  }
  std::function<bool(unsigned, unsigned, unsigned)> same = [&](unsigned left,
                                                               unsigned right,
                                                               unsigned depth) {
    if (depth > types.work.limits.expressionDepth)
      return types.fail("source.limit", "finite formation depth", span);
    if (!types.charge(1, span))
      return false;
    if (left == right)
      return true;
    const auto &a = shape.nodes[left], &b = shape.nodes[right];
    const auto &x = cards[left], &y = cards[right];
    if (x.fixed && y.fixed)
      return *x.fixed == *y.fixed ||
             types.fail("source.data-bound", "total zip extents differ", span);
    if (x.container && y.container)
      return evidence.equalExtent(*x.container, x.axis, *y.container, y.axis);
    if (a.kind == Kind::Zip)
      return same(a.children.front(), right, depth + 1);
    if (b.kind == Kind::Zip)
      return same(left, b.children.front(), depth + 1);
    if (a.kind == Kind::Product && b.kind == Kind::Product &&
        a.children.size() == b.children.size()) {
      for (unsigned i = 0; i < a.children.size(); ++i)
        if (!same(a.children[i], b.children[i], depth + 1))
          return false;
      return true;
    }
    if (a.kind == Kind::Range && b.kind == Kind::Range &&
        evidence.same(a.operands[0], b.operands[0]) &&
        evidence.same(a.operands[1], b.operands[1]))
      return true;
    if (a.kind == Kind::MatrixCoordinates &&
        b.kind == Kind::MatrixCoordinates) {
      for (unsigned axis = 0; axis < 2; ++axis)
        if (!evidence.equalExtent(a.operands[0], axis, b.operands[0], axis))
          return false;
      return true;
    }
    return types.fail("source.data-bound",
                      "total zip requires equal cardinality evidence", span);
  };
  if (total)
    for (const auto &node : shape.nodes) {
      if (node.kind == Kind::Zip)
        for (auto child : ArrayRef(node.children).drop_front())
          if (!same(node.children.front(), child, 0))
            return false;
      if (node.kind == Kind::MatrixRow || node.kind == Kind::MatrixColumn)
        if (!evidence.bound(node.operands[1], node.operands[0],
                            node.kind == Kind::MatrixRow ? 0u : 1u))
          return false;
    }
  if (finite.kind == FiniteApplication::Kind::Collect &&
      result.kind == Type::Kind::Builtin && result.domain == "field_array") {
    const auto &size = result.arguments[1].dimension;
    auto count = cards[shape.result].fixed;
    if (finite.predicate || !size.isClosed() || !count ||
        *count != size.closedValue())
      return types.fail("source.data-bound",
                        "fixed collection needs exact unfiltered cardinality",
                        span);
  }
  return true;
}
} // namespace zkc::language::detail
