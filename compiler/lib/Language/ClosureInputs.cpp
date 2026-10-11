#include "ClosureInputs.h"
using namespace llvm;
namespace zkc::language::detail {
std::optional<ClosureInputs>
closeInputs(Semantics &types, const Body &body,
            ArrayRef<std::optional<ValueId>> authored,
            ArrayRef<ValueId> captures, Span span, ValueOrigins *cache) {
  if (!types.charge(authored.size() + captures.size() + 1, span))
    return {};
  ClosureInputs result;
  result.operands.assign(authored.begin(), authored.end());
  ValueOrigins localOrigins(types, body);
  auto &origins = cache ? *cache : localOrigins;
  if (!origins.describes(body)) {
    types.fail("source.closure-inputs",
               "origin cache belongs to a different body", span);
    return {};
  }
  std::map<ValueOrigin, unsigned> selected;
  auto select = [&](ValueId value, unsigned fresh,
                    bool capture) -> std::optional<unsigned> {
    if (value.index >= body.values.size()) {
      types.fail("source.closure-inputs", "capture operand is outside its body",
                 span);
      return {};
    }
    auto permissions = types.permissions(body.values[value.index].type, span);
    if (!permissions)
      return {};
    if (!permissions->copy || !permissions->drop) {
      if (!capture)
        return fresh;
      types.fail("source.closure-inputs",
                 "hidden captures require Copy and Drop", span);
      return {};
    }
    auto origin = origins.get(value, span);
    if (!origin)
      return {};
    uint64_t levels = 1;
    for (auto count = selected.size(); count > 1; count >>= 1)
      ++levels;
    if (!types.charge((origin->second.size() + 1) * levels, span))
      return {};
    auto [found, inserted] = selected.emplace(std::move(*origin), fresh);
    if (!inserted && body.values[result.operands[found->second]->index].type !=
                         body.values[value.index].type) {
      types.fail("source.closure-inputs",
                 "one captured place has different types", span);
      return {};
    }
    return found->second;
  };
  for (unsigned i = 0; i < authored.size(); ++i) {
    auto canonical = authored[i] ? select(*authored[i], i, false)
                                 : std::optional<unsigned>(i);
    if (!canonical)
      return {};
    result.layout.inputs.push_back(*canonical);
  }
  for (auto capture : captures) {
    auto port = select(capture, result.operands.size(), true);
    if (!port)
      return {};
    if (*port == result.operands.size())
      result.operands.push_back(capture);
    result.layout.captures.push_back(*port);
  }
  return result;
}
std::optional<std::vector<std::optional<ValueId>>>
bindClosureInputs(Semantics &types, const Body &body,
                  ArrayRef<std::optional<ValueId>> authored,
                  ArrayRef<ValueId> captures, const ClosureLayout &layout,
                  unsigned ports, Span span, ValueOrigins *cache) {
  auto refuse = [&]() {
    types.fail("source.closure-inputs",
               "closed input aliases differ from caller SSA places", span);
    return std::optional<std::vector<std::optional<ValueId>>>{};
  };
  if (layout.inputs.size() != authored.size() ||
      layout.captures.size() != captures.size() || ports < authored.size() ||
      ports > authored.size() + captures.size())
    return refuse();
  if (!types.charge(ports + captures.size() + 1, span))
    return {};
  std::vector<std::optional<ValueId>> result(authored.begin(), authored.end());
  result.resize(ports);
  ValueOrigins localOrigins(types, body);
  auto &origins = cache ? *cache : localOrigins;
  if (!origins.describes(body)) {
    types.fail("source.closure-inputs",
               "origin cache belongs to a different body", span);
    return {};
  }
  auto equal = [&](ValueId a, ValueId b) {
    if (a.index >= body.values.size() || b.index >= body.values.size() ||
        body.values[a.index].type != body.values[b.index].type)
      return false;
    auto permissions = types.permissions(body.values[a.index].type, span);
    if (!permissions || !permissions->copy || !permissions->drop)
      return false;
    auto x = origins.get(a, span), y = origins.get(b, span);
    return x && y && *x == *y;
  };
  for (unsigned i = 0; i < authored.size(); ++i) {
    auto target = layout.inputs[i];
    if (target > i || layout.inputs[target] != target ||
        (target != i && (!authored[i] || !authored[target] ||
                         !equal(*authored[i], *authored[target]))))
      return refuse();
  }
  for (unsigned i = 0; i < captures.size(); ++i) {
    auto target = layout.captures[i];
    if (target >= result.size() ||
        (target < authored.size() &&
         (layout.inputs[target] != target || !authored[target])))
      return refuse();
    if (result[target]) {
      if (!equal(*result[target], captures[i]))
        return refuse();
    } else {
      if (!equal(captures[i], captures[i]))
        return refuse();
      result[target] = captures[i];
    }
  }
  for (unsigned i = authored.size(); i < result.size(); ++i)
    if (!result[i])
      return refuse();
  return result;
}
} // namespace zkc::language::detail
