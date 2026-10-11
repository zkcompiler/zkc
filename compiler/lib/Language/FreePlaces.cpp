#include "FreePlaces.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
std::optional<RegionInputs>
queryFreePlaces(Semantics &types, const SyntaxDeclaration &syntax,
                const Expression &control,
                const FreePlaceEnvironment &environment) {
  RegionInputs result;
  // A free input is a read before whole assignment on some continuing path.
  // Merely mentioning a restored binding must not capture its old moved value.
  struct Flow {
    std::set<BindingId> assigned;
    bool stopped = false;
  };
  std::function<bool(uint32_t, unsigned, Flow &)> visit;
  std::function<bool(uint32_t, unsigned, Flow &)> region =
      [&](uint32_t id, unsigned depth, Flow &flow) {
        const auto &source = syntax.bodies[id];
        if (depth > types.work.limits.expressionDepth ||
            !types.charge(1, source.span))
          return types.diagnostic
                     ? false
                     : types.fail("source.limit", "region summary depth",
                                  source.span);
        for (const auto &s : source.statements) {
          if (flow.stopped)
            break; // Body checking diagnoses the unreachable suffix.
          if (!visit(s.expression, depth + 1, flow))
            return false;
          if (!flow.stopped && s.kind == Statement::Kind::Assign &&
              environment.data.count(*s.pattern.binding)) {
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
    if (depth > types.work.limits.expressionDepth ||
        !types.charge(1, expr.span))
      return types.diagnostic ? false
                              : types.fail("source.limit",
                                           "region summary depth", expr.span);
    if (expr.kind == Expression::Kind::Name ||
        expr.kind == Expression::Kind::Projection) {
      auto root = id;
      while (syntax.expressions[root].kind == Expression::Kind::Projection) {
        if (!types.charge(1, expr.span))
          return false;
        root = syntax.expressions[root].children.front();
      }
      const auto &name = syntax.expressions[root];
      if (name.kind == Expression::Kind::Name && name.binding) {
        if (environment.domains.count(*name.binding)) {
          result.domains.insert(*name.binding);
          return true;
        }
        if (environment.scoped.count(*name.binding)) {
          result.scoped.insert(*name.binding);
          return true;
        }
        if (environment.services.count(*name.binding)) {
          result.services.insert(*name.binding);
          return true;
        }
        if (environment.data.count(*name.binding)) {
          auto place = environment.place(id);
          if (!place)
            return false;
          if (!flow.assigned.count(place->first)) {
            FreePlace capture{place->first, place->second};
            result.places.insert(capture);
            result.occurrences.try_emplace(capture, expr.span);
          }
          return true;
        }
      }
    }
    if (expr.binding && environment.scoped.count(*expr.binding))
      result.scoped.insert(*expr.binding);
    if (expr.kind == Expression::Kind::Lambda) {
      // Capture discovery visits deferred code without executing its flow.
      for (auto id : expr.regions) {
        if (!types.charge(flow.assigned.size() + 1, expr.span))
          return false;
        Flow deferred{flow.assigned, false};
        if (!region(id, depth + 1, deferred))
          return false;
      }
      return true;
    }
    for (unsigned i = 0; i < expr.children.size(); ++i) {
      if ((expr.kind == Expression::Kind::And ||
           expr.kind == Expression::Kind::Or) &&
          i == 1)
        continue;
      auto child = expr.children[i];
      if (!visit(child, depth + 1, flow))
        return false;
      if (flow.stopped)
        return true;
    }
    if (expr.kind == Expression::Kind::Block)
      return region(expr.regions.front(), depth + 1, flow);
    std::optional<Flow> joined;
    for (auto body : expr.regions) {
      if (!types.charge(flow.assigned.size() + 1, expr.span))
        return false;
      auto arm = flow;
      if (!region(body, depth + 1, arm))
        return false;
      if (arm.stopped)
        continue;
      if (!joined)
        joined = std::move(arm);
      else {
        if (!types.charge(joined->assigned.size() + arm.assigned.size(),
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
      if (!types.charge(last.path.size() + 1, control.span))
        return {};
      if (last.binding == place.binding &&
          last.path.size() <= place.path.size() &&
          std::equal(last.path.begin(), last.path.end(), place.path.begin())) {
        if (result.occurrences.at(place).begin <
            result.occurrences.at(last).begin)
          result.occurrences[last] = result.occurrences.at(place);
        continue;
      }
    }
    minimal.insert(place);
  }
  result.places = std::move(minimal);
  return result;
}
} // namespace zkc::language::detail
