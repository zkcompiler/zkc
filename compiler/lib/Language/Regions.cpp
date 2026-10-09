#include "BodyCheck.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
std::optional<BodyChecker::RegionInputs>
BodyChecker::regionInputs(const Expression &control) {
  RegionInputs result;
  // A free input is a read before whole assignment on some continuing path.
  // Merely mentioning a restored binding must not capture its old moved value.
  struct Flow {
    std::set<BindingId> assigned;
    bool stopped = false;
  };
  std::function<bool(uint32_t, unsigned, Flow &)> visit;
  std::function<bool(uint32_t, unsigned, Flow &)> region = [&](uint32_t id,
                                                               unsigned depth,
                                                               Flow &flow) {
    const auto &source = syntax.bodies[id];
    if (depth > checker.work.limits.expressionDepth ||
        !checker.types.charge(1, source.span))
      return checker.types.diagnostic
                 ? false
                 : fail("source.limit", "region summary depth", source.span);
    for (const auto &s : source.statements) {
      if (flow.stopped)
        break; // Body checking diagnoses the unreachable suffix.
      if (!visit(s.expression, depth + 1, flow))
        return false;
      if (!flow.stopped && s.kind == Statement::Kind::Assign &&
          bindings.count(*s.pattern.binding)) {
        result.writes.insert(*s.pattern.binding);
        flow.assigned.insert(*s.pattern.binding);
      }
    }
    for (auto &[name, value] : source.results) {
      if (flow.stopped)
        break;
      if (!visit(value, depth + 1, flow))
        return false;
    }
    flow.stopped |= source.stopped;
    return true;
  };
  visit = [&](uint32_t id, unsigned depth, Flow &flow) {
    const auto &expr = syntax.expressions[id];
    if (depth > checker.work.limits.expressionDepth ||
        !checker.types.charge(1, expr.span))
      return checker.types.diagnostic
                 ? false
                 : fail("source.limit", "region summary depth", expr.span);
    if (expr.kind == Expression::Kind::Name ||
        expr.kind == Expression::Kind::Projection) {
      auto root = id;
      while (syntax.expressions[root].kind == Expression::Kind::Projection) {
        if (!checker.types.charge(1, expr.span))
          return false;
        root = syntax.expressions[root].children.front();
      }
      const auto &name = syntax.expressions[root];
      if (name.kind == Expression::Kind::Name && name.binding) {
        if (services.count(*name.binding)) {
          result.services.insert(*name.binding);
          return true;
        }
        if (bindings.count(*name.binding)) {
          auto place = sourcePlace(id);
          if (!place)
            return false;
          if (!flow.assigned.count(place->first))
            result.places.insert({place->first, place->second});
          return true;
        }
      }
    }
    for (auto id : expr.serviceBindings)
      if (services.count(id))
        result.services.insert(id);
    for (auto child : expr.children) {
      if (!visit(child, depth + 1, flow))
        return false;
      if (flow.stopped)
        return true;
    }
    if (expr.kind == Expression::Kind::Block)
      return region(expr.regions.front(), depth + 1, flow);
    std::optional<Flow> joined;
    for (auto body : expr.regions) {
      if (!checker.types.charge(flow.assigned.size() + 1, expr.span))
        return false;
      auto arm = flow;
      if (!region(body, depth + 1, arm))
        return false;
      if (arm.stopped)
        continue;
      if (!joined)
        joined = std::move(arm);
      else {
        if (!checker.types.charge(joined->assigned.size() + arm.assigned.size(),
                                  expr.span))
          return false;
        std::set<BindingId> common;
        std::set_intersection(joined->assigned.begin(), joined->assigned.end(),
                              arm.assigned.begin(), arm.assigned.end(),
                              std::inserter(common, common.end()));
        joined->assigned = std::move(common);
      }
    }
    if (!expr.regions.empty() && expr.kind != Expression::Kind::For) {
      if (joined)
        flow = std::move(*joined);
      else
        flow.stopped = true;
    }
    return true;
  };
  for (auto id : control.regions) {
    Flow flow;
    if (!region(id, 1, flow))
      return {};
  }
  // A whole-place capture subsumes its descendants. The sorted antichain avoids
  // manufacturing duplicate moves for overlapping source projections.
  std::set<FreePlace> minimal;
  for (const auto &place : result.places) {
    if (!minimal.empty()) {
      const auto &last = *minimal.rbegin();
      if (!checker.types.charge(last.path.size() + 1, control.span))
        return {};
      if (last.binding == place.binding &&
          last.path.size() <= place.path.size() &&
          std::equal(last.path.begin(), last.path.end(), place.path.begin()))
        continue;
    }
    minimal.insert(place);
  }
  result.places = std::move(minimal);
  return result;
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
