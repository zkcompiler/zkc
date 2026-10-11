#include "FiniteFormation.h"
#include "MathematicalFacts.h"
#include "zkc/Contracts/FiniteCardinality.h"
using namespace llvm;
namespace zkc::language::detail {
bool checkFiniteFormation(Semantics &types, const FiniteComputation &finite,
                          const Type &result, bool total, Span span,
                          const FiniteFormationEvidence &evidence) {
  const auto &shape = *finite.domain;
  facts::Work work([&](uint64_t amount) {
    return !types.diagnostic && types.charge(amount, span);
  });
  using Kind = DomainBinding::Kind;
  auto node = [&](facts::DomainRef id) {
    const auto &source = shape.nodes[id];
    facts::DomainNode view;
    view.children = source.children.size();
    switch (source.kind) {
    case Kind::Elements:
    case Kind::SourceArray:
    case Kind::Indices:
    case Kind::MatrixRow:
    case Kind::MatrixColumn:
      view.kind = facts::DomainKind::Extent;
      view.extent = {source.operands.front().index,
                     source.kind == Kind::Indices     ? source.axis
                     : source.kind == Kind::MatrixRow ? 1u
                                                      : 0u};
      break;
    case Kind::Range:
      view.kind = facts::DomainKind::Range;
      view.lower = source.operands[0].index;
      view.upper = source.operands[1].index;
      break;
    case Kind::Zip:
      view.kind = facts::DomainKind::Zip;
      break;
    case Kind::Product:
      view.kind = facts::DomainKind::Product;
      break;
    case Kind::MatrixCoordinates:
      view.kind = facts::DomainKind::MatrixCoordinates;
      view.extent.value = source.operands.front().index;
      break;
    case Kind::Parameter:
    case Kind::Application:
      break;
    }
    return view;
  };
  auto child = [&](facts::DomainRef id, size_t index) -> facts::DomainRef {
    return shape.nodes[id].children[index];
  };
  auto exhausted = [&] {
    if (types.diagnostic && types.diagnostic->code == "source.limit")
      work.exhaust();
    return work.exhausted();
  };
  auto extent = [&](facts::DomainExtent leaf,
                    unsigned) -> facts::Result<facts::Cardinality> {
    std::optional<uint64_t> count;
    if (total) {
      count = evidence.extent({unsigned(leaf.value)}, leaf.axis);
    } else if (leaf.value < shape.inputs.size()) {
      // Local finite declarations are checked on formals, not call actuals.
      // Source arrays become dynamic Sequence formals during emission; only
      // native type extents survive that boundary without additional evidence.
      const auto &input = shape.inputs[leaf.value];
      auto *size = input.kind == Type::Kind::Builtin
                       ? staticExtent(input, leaf.axis)
                       : nullptr;
      if (size && size->isClosed())
        count = size->closedValue();
    }
    if (exhausted())
      return {facts::Status::Capacity, std::nullopt};
    return count ? facts::Result<facts::Cardinality>{facts::Status::Proven,
                                                     facts::Cardinality{*count}}
                 : facts::Result<facts::Cardinality>{};
  };
  auto integer = [&](facts::DomainLeaf leaf,
                     unsigned) -> facts::Result<uint64_t> {
    // Local range endpoints are declaration parameters, even for literals at
    // an apply site. Their actual values cannot justify a fixed declaration.
    auto value = total ? evidence.constant({unsigned(leaf)}) : std::nullopt;
    if (exhausted())
      return {facts::Status::Capacity, std::nullopt};
    return value ? facts::Result<uint64_t>{facts::Status::Proven, *value}
                 : facts::Result<uint64_t>{};
  };
  auto same = [&](facts::DomainLeaf a, facts::DomainLeaf b, unsigned) {
    bool proven = evidence.same({unsigned(a)}, {unsigned(b)});
    if (exhausted())
      return facts::Status::Capacity;
    return proven ? facts::Status::Proven : facts::Status::Unknown;
  };
  auto equal = [&](facts::DomainExtent a, facts::DomainExtent b, unsigned) {
    bool proven = evidence.equalExtent({unsigned(a.value)}, a.axis,
                                       {unsigned(b.value)}, b.axis);
    if (exhausted())
      return facts::Status::Capacity;
    return proven ? facts::Status::Proven : facts::Status::Unknown;
  };
  facts::DomainCardinality cardinality(
      work, {node, child, extent, integer, same, equal},
      types.work.limits.expressionDepth);
  auto established = [&](facts::Status status, StringRef message) {
    if (status == facts::Status::Proven)
      return true;
    if (status == facts::Status::Capacity)
      return types.fail("source.limit", "finite formation work or depth", span);
    return types.fail("source.data-bound", message, span);
  };
  // Check every constructor's admission, even when the result count is zero
  // or the selected result does not reach an earlier constructor.
  for (const auto &source : shape.nodes) {
    if (!work.charge(source.operands.size() + source.children.size() + 1))
      return established(facts::Status::Capacity, "finite formation work");
    if (!total)
      continue;
    if (source.kind == Kind::Zip)
      for (auto selected : ArrayRef(source.children).drop_front())
        if (!established(cardinality.equal(source.children.front(), selected),
                         "total zip requires equal cardinality evidence"))
          return false;
    if (source.kind == Kind::MatrixRow || source.kind == Kind::MatrixColumn)
      if (!evidence.bound(source.operands[1], source.operands[0],
                          source.kind == Kind::MatrixRow ? 0u : 1u))
        return false;
  }
  if (finite.kind == FiniteApplication::Kind::Collect &&
      result.kind == Type::Kind::Builtin && result.domain == "field_array") {
    const auto &size = result.arguments[1].dimension;
    auto count = cardinality.exact(shape.result);
    if (count.status == facts::Status::Capacity)
      return established(count.status, "finite formation work");
    if (finite.predicate || !size.isClosed() ||
        count.status != facts::Status::Proven ||
        *count.value != size.closedValue())
      return types.fail("source.data-bound",
                        "fixed collection needs exact unfiltered cardinality",
                        span);
  }
  return true;
}
} // namespace zkc::language::detail
