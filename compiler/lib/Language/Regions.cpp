#include "BodyCheck.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
std::optional<RegionInputs>
BodyChecker::regionInputs(const Expression &control) {
  FreePlaceEnvironment environment;
  for (const auto &[id, state] : bindings) {
    (void)state;
    environment.data.insert(id);
  }
  for (const auto &[id, state] : services) {
    (void)state;
    environment.services.insert(id);
  }
  for (const auto &[id, state] : scoped) {
    (void)state;
    environment.scoped.insert(id);
  }
  for (const auto &[id, state] : domains) {
    (void)state;
    environment.domains.insert(id);
  }
  environment.place = [&](uint32_t id) { return sourcePlace(id, 1, true); };
  return queryFreePlaces(checker.types, syntax, control, environment);
}
std::optional<std::set<BindingId>>
BodyChecker::regionStates(const RegionInputs &inputs, Span span) {
  if (!checker.types.charge(inputs.writes.size() + 1, span))
    return {};
  // Only assignment needs a state successor. Read-only places are captures,
  // preserving their identity and data facts regardless of usage properties.
  return inputs.writes;
}
std::optional<ValueId> BodyChecker::capturePlace(const FreePlace &source,
                                                 Span span) {
  auto p = place(source, span);
  if (!p)
    return {};
  auto [value, path] = *p;
  return project(value, path, span);
}
bool BodyChecker::importPlace(BodyChecker &nested, const FreePlace &place,
                              ValueId operand, Span span) {
  const auto &source = bindings.at(place.binding);
  const auto &value = body.values[operand.index];
  auto input = nested.input(value.type, value.components, span);
  if (!input)
    return false;
  auto [it, inserted] = nested.bindings.try_emplace(
      place.binding, BindingState{source.type, source.roles, {}, {}});
  if (place.path.empty())
    it->second.value = *input;
  else
    it->second.pieces.emplace_back(place.path, *input);
  return true;
}
bool BodyChecker::inheritBinding(BodyChecker &nested, BindingId id, Span span) {
  const auto &state = bindings.at(id);
  return nested.addInput(id, state.type, state.roles, span);
}
} // namespace zkc::language::detail
