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
  environment.place = [&](uint32_t id) { return sourcePlace(id); };
  return queryFreePlaces(checker.types, syntax, control, environment);
}
std::optional<std::set<BindingId>>
BodyChecker::regionStates(const RegionInputs &inputs, Span span) {
  auto states = inputs.writes;
  for (const auto &place : inputs.places) {
    const auto &state = bindings.at(place.binding);
    auto caps = checker.types.permissions(state.type, span, &decl);
    if (!caps)
      return {};
    // A partially moved root can only supply its remaining places. Assignment
    // may restore the whole binding in a branch, but loops need an initial
    // root.
    if (syntax.bindings[place.binding.index].mutableBinding && !caps->copy &&
        state.value && available(*state.value))
      states.insert(place.binding);
  }
  return states;
}
std::optional<ValueId> BodyChecker::capturePlace(const FreePlace &source,
                                                 Span span) {
  auto p = place(source, span);
  if (!p)
    return {};
  auto [value, path] = *p;
  auto type = projected(body.values[value.index].type, path, span);
  auto caps =
      type ? checker.types.permissions(*type, span, &decl) : std::nullopt;
  if (!caps)
    return {};
  if (caps->copy && !caps->drop) {
    // Inferred copies introduce no authored obligation. Branches propagate
    // guaranteed uses back to this place; possibly empty loops cannot do so.
    if (!available(value, path)) {
      fail("source.move", "capture overlaps a moved place", span);
      return {};
    }
    return emit(Projection{value, path}, *type,
                body.values[value.index].components, span);
  }
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
