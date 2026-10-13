#include "ValueOrigins.h"
using namespace llvm;
namespace zkc::language::detail {
bool ValueOrigins::initialize() {
  if (initialized)
    return true;
  if (!types.charge(body.values.size() + body.operations.size() + 1, {}))
    return false;
  producers.resize(body.values.size());
  origins.resize(body.values.size());
  for (const auto &op : body.operations)
    for (auto result : op.results) {
      if (result.index >= producers.size() || producers[result.index])
        return types.fail("source.value-origin", "invalid SSA producer",
                          op.span);
      producers[result.index] = &op;
    }
  initialized = true;
  return true;
}
const Operation *ValueOrigins::producer(ValueId id, Span span) {
  if (!initialize() || !types.charge(1, span))
    return nullptr;
  if (id.index >= producers.size()) {
    types.fail("source.value-origin", "SSA value is outside its body", span);
    return nullptr;
  }
  return producers[id.index];
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
    const auto *definition = producers[value.index];
    if (const auto *projection =
            definition ? std::get_if<Projection>(&definition->action) : nullptr)
      value = projection->input;
    else {
      origins[value.index] = ValueOrigin{value.index, {}};
      break;
    }
  }
  for (auto it = chain.rbegin(); it != chain.rend(); ++it) {
    auto current = it->index;
    const auto *definition = producers[current];
    if (const auto *projection =
            definition ? std::get_if<Projection>(&definition->action)
                       : nullptr) {
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
std::optional<ValueOrigin>
ValueOrigins::select(ValueId id, ArrayRef<unsigned> path, Span span) {
  auto origin = get(id, span);
  if (!origin)
    return {};
  if (path.empty() && origin->second.empty())
    return origin;
  if (!types.charge(path.size(), span))
    return {};
  origin->second.insert(origin->second.end(), path.begin(), path.end());
  std::vector<ValueOrigin> chain;
  while (true) {
    if (!types.charge(origin->second.size() + 1, span))
      return {};
    if (auto found = selections.find(*origin); found != selections.end()) {
      origin = found->second;
      break;
    }
    chain.push_back(*origin);
    const auto *definition = producers[origin->first];
    const auto *aggregate =
        definition ? std::get_if<Construct>(&definition->action) : nullptr;
    if (!aggregate || aggregate->kind != Construct::Kind::Aggregate ||
        origin->second.empty())
      break;
    unsigned field = origin->second.front();
    if (field >= aggregate->operands.size()) {
      types.fail("source.value-origin",
                 "record projection is outside its fields", span);
      return {};
    }
    auto selected = get(aggregate->operands[field], span);
    if (!selected)
      return {};
    selected->second.insert(selected->second.end(), origin->second.begin() + 1,
                            origin->second.end());
    origin = std::move(selected);
  }
  for (auto &entry : chain)
    selections.emplace(std::move(entry), *origin);
  return origin;
}
} // namespace zkc::language::detail
