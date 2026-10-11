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
std::optional<ValueOrigin> ValueOrigins::get(ValueId value, Span span) {
  if (!initialize())
    return {};
  const auto requested = value;
  std::vector<ValueId> chain;
  // Empty-path projections include ordinary let aliases. Their chain length
  // is bounded by SSA work, not by syntactic expression nesting or the stack.
  while (true) {
    if (!types.charge(1, span))
      return {};
    if (value.index >= origins.size()) {
      types.fail("source.value-origin", "SSA operand is outside its body",
                 span);
      return {};
    }
    if (origins[value.index])
      break;
    if (!active.insert(value.index).second) {
      types.fail("source.value-origin", "cyclic SSA projection", span);
      return {};
    }
    chain.push_back(value);
    if (const auto *projection = projections[value.index])
      value = projection->input;
    else {
      origins[value.index] = ValueOrigin{value.index, {}};
      break;
    }
  }
  for (auto it = chain.rbegin(); it != chain.rend(); ++it) {
    auto current = it->index;
    if (const auto *projection = projections[current]) {
      const auto &parent = *origins[projection->input.index];
      if (!types.charge(parent.second.size() + projection->path.size() + 1,
                        span))
        return {};
      ValueOrigin result = parent;
      result.second.insert(result.second.end(), projection->path.begin(),
                           projection->path.end());
      origins[current] = std::move(result);
    }
    active.erase(current);
  }
  if (!types.charge(origins[requested.index]->second.size() + 1, span))
    return {};
  return origins[requested.index];
}
} // namespace zkc::language::detail
