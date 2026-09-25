#include "Aggregates.h"
namespace zkc::frontend {
namespace {
bool sameNode(const AggregateShape &a, const AggregateShape &b) {
  return a.product == b.product && a.array == b.array && a.arity == b.arity &&
         a.declaration == b.declaration && a.paths == b.paths;
}
} // namespace
bool sameAggregateStructure(const AggregateShape &a, const AggregateShape &b) {
  if (!sameNode(a, b) || a.nested.size() != b.nested.size())
    return false;
  // `nested` is a flattened path index, so visiting every entry checks the
  // whole tree without recursively revisiting the same descendants.
  for (size_t i = 0; i < a.nested.size(); ++i)
    if (a.nested[i].first != b.nested[i].first ||
        !sameNode(a.nested[i].second, b.nested[i].second))
      return false;
  return true;
}
} // namespace zkc::frontend
