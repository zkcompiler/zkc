#include "MathematicalFacts.h"
using namespace llvm;
namespace zkc::language::detail {
const Natural *staticExtent(const Type &type, unsigned axis) {
  if (axis)
    return nullptr;
  if (type.kind == Type::Kind::Array)
    return &type.dimension;
  if (type.kind == Type::Kind::Builtin && type.domain == "field_array" &&
      type.arguments.size() == 2)
    return &type.arguments[1].dimension;
  return nullptr;
}
MathematicalFacts::MathematicalFacts(Semantics &types)
    : types(types), work([this](uint64_t amount) {
        return !this->types.diagnostic && this->types.charge(amount, span);
      }),
      snapshot(work), current(snapshot.root()) {}
facts::Status MathematicalFacts::enter(Span at) {
  span = at;
  auto nested = snapshot.fork(current);
  if (nested.status == facts::Status::Proven)
    current = *nested.value;
  return nested.status;
}
facts::Status MathematicalFacts::record(const ValueOrigin &origin,
                                        const Type &type, Span at) {
  span = at;
  if (!work.charge())
    return facts::Status::Capacity;
  auto *dimension = staticExtent(type, 0);
  if (!dimension)
    return facts::Status::Proven;
  if (!types.chargeType(type, span))
    return facts::Status::Capacity;
  auto value = snapshot.intern(origin.first, origin.second);
  if (value.status != facts::Status::Proven)
    return value.status;
  facts::Extent extent{*value.value, 0};
  if (dimension->isClosed())
    return snapshot.addExtent(current, extent, dimension->closedValue(),
                              facts::Premise::Formation);
  // Equality of normalized source polynomials is an explicit formation
  // premise, including symbolic dimensions with no runtime ui64 value.
  auto [representative, inserted] =
      dimensions.emplace(dimension->terms(), extent);
  if (inserted)
    return facts::Status::Proven;
  return snapshot.addEquality(current, extent, representative->second,
                              facts::Premise::Formation);
}
facts::Status MathematicalFacts::constant(const ValueOrigin &origin,
                                          uint64_t number, Span at) {
  span = at;
  auto value = snapshot.intern(origin.first, origin.second);
  if (value.status != facts::Status::Proven)
    return value.status;
  return snapshot.addInteger(current, *value.value, number,
                             facts::Premise::Result);
}
facts::Status MathematicalFacts::assume(const SourceDataFact &fact, Span at) {
  span = at;
  auto left = snapshot.intern(fact.left.first, fact.left.second);
  if (left.status != facts::Status::Proven)
    return left.status;
  auto right = snapshot.intern(fact.right.first, fact.right.second);
  if (right.status != facts::Status::Proven)
    return right.status;
  if (fact.kind == DataPrecondition::Kind::EqualExtent)
    return snapshot.addEquality(current, {*left.value, fact.leftAxis},
                                {*right.value, fact.rightAxis},
                                facts::Premise::Formation);
  return snapshot.addBound(current, *left.value, {*right.value, fact.rightAxis},
                           facts::Premise::Formation);
}
facts::Result<facts::Cardinality>
MathematicalFacts::cardinality(const ValueOrigin &origin, unsigned axis,
                               Span at) {
  span = at;
  auto value = snapshot.intern(origin.first, origin.second);
  if (value.status != facts::Status::Proven)
    return {value.status, std::nullopt};
  return snapshot.cardinality(current, {*value.value, axis});
}
facts::Status MathematicalFacts::resultCardinality(const ValueOrigin &origin,
                                                   facts::Cardinality count,
                                                   Span at) {
  span = at;
  auto value = snapshot.intern(origin.first, origin.second);
  if (value.status != facts::Status::Proven)
    return value.status;
  return snapshot.addCardinality(current, {*value.value, 0}, count,
                                 facts::Premise::Result);
}
facts::Status MathematicalFacts::resultExtent(const ValueOrigin &origin,
                                              const ValueOrigin &container,
                                              unsigned axis, Span at) {
  span = at;
  auto value = snapshot.intern(origin.first, origin.second);
  if (value.status != facts::Status::Proven)
    return value.status;
  auto source = snapshot.intern(container.first, container.second);
  if (source.status != facts::Status::Proven)
    return source.status;
  return snapshot.addEquality(current, {*value.value, 0}, {*source.value, axis},
                              facts::Premise::Result);
}
facts::Status MathematicalFacts::prove(const SourceDataFact &fact, Span at) {
  span = at;
  auto left = snapshot.intern(fact.left.first, fact.left.second);
  if (left.status != facts::Status::Proven)
    return left.status;
  auto right = snapshot.intern(fact.right.first, fact.right.second);
  if (right.status != facts::Status::Proven)
    return right.status;
  if (fact.kind == DataPrecondition::Kind::EqualExtent)
    return snapshot.equal(current, {*left.value, fact.leftAxis},
                          {*right.value, fact.rightAxis});
  return snapshot.bound(current, *left.value, {*right.value, fact.rightAxis});
}
} // namespace zkc::language::detail
