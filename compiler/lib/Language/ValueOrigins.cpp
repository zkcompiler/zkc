#include "ValueOrigins.h"
using namespace llvm;
namespace zkc::language::detail {
bool ValueOrigins::initialize() {
  if (initialized)
    return true;
  if (!types.charge(body.values.size() + body.operations.size() + 1, {}))
    return false;
  projections.resize(body.values.size());
  origins.resize(body.values.size());
  for (const auto &op : body.operations)
    if (const auto *projection = std::get_if<Projection>(&op.action)) {
      if (op.results.size() != 1 ||
          op.results.front().index >= projections.size() ||
          projections[op.results.front().index])
        return types.fail("source.value-origin", "invalid projection producer",
                          op.span);
      projections[op.results.front().index] = projection;
    }
  initialized = true;
  return true;
}
std::optional<ValueOrigin> ValueOrigins::get(ValueId value, Span span,
                                             unsigned depth) {
  if (!initialize() || !types.charge(1, span))
    return {};
  if (depth > types.work.limits.expressionDepth) {
    types.fail("source.limit", "SSA projection origin depth exceeded", span);
    return {};
  }
  if (value.index >= origins.size()) {
    types.fail("source.value-origin", "SSA operand is outside its body", span);
    return {};
  }
  if (origins[value.index]) {
    if (!types.charge(origins[value.index]->second.size() + 1, span))
      return {};
    return origins[value.index];
  }
  if (!active.insert(value.index).second) {
    types.fail("source.value-origin", "cyclic SSA projection", span);
    return {};
  }
  ValueOrigin result{value.index, {}};
  if (const auto *projection = projections[value.index]) {
    auto parent = get(projection->input, span, depth + 1);
    if (!parent ||
        !types.charge(parent->second.size() + projection->path.size() + 1,
                      span))
      return {};
    result = std::move(*parent);
    result.second.insert(result.second.end(), projection->path.begin(),
                         projection->path.end());
  }
  if (!types.charge(result.second.size() + 1, span))
    return {};
  active.erase(value.index);
  origins[value.index] = result;
  return result;
}
} // namespace zkc::language::detail
