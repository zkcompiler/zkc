#include "BodyCheck.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
bool BodyChecker::repeat(const Expression &expr) {
  if (!protocol() || !expr.roles || expr.arguments.size() != 1)
    return fail("source.mode",
                "protocol for requires explicit roles(...) max N", expr.span);
  const auto &lower = syntax.expressions[expr.children.front()];
  if (lower.kind != Expression::Kind::Decimal || lower.text != "0")
    return fail("source.bound", "protocol for starts at literal zero",
                lower.span);
  auto roles = checker.roles(decl, *expr.roles, expr.span);
  if (!roles || !active(*roles, expr.span))
    return false;
  auto maximum = checker.type(decl, expr.arguments.front());
  if (!maximum)
    return false;
  if (maximum->kind != Type::Kind::Natural)
    return fail("source.bound", "loop maximum must be a static natural",
                expr.span);
  if (maximum->dimension.isClosed() &&
      maximum->dimension.closedValue() > 1048576)
    return fail("source.bound", "loop maximum exceeds installed limit",
                expr.span);
  auto count = expression(expr.children[1], Type(Type::Kind::Index));
  if (!count || !use(*count, expr.span))
    return false;
  const auto &countRoles = body.values[count->index].components;
  if (!std::includes(countRoles.begin(), countRoles.end(), roles->begin(),
                     roles->end()))
    return fail("source.roles",
                "loop count must be available at every loop participant",
                expr.span);
  auto summary = regionInputs(expr);
  if (!summary)
    return false;
  auto selectedStates = regionStates(*summary, expr.span);
  if (!selectedStates)
    return false;
  const auto &states = *selectedStates;
  ProtocolRepeat operation{*roles, *count, maximum->dimension, {}, {}, {}, {}};
  auto region = std::make_shared<Body>();
  region->mode = Body::Mode::Protocol;
  BodyChecker nested(checker, decl, syntax, *region, callDepth);
  nested.activeRoles = *roles;
  auto index = nested.input(Type(Type::Kind::Index), *roles, expr.index.span);
  if (!index)
    return false;
  if (expr.index.binding)
    nested.bindings.emplace(
        *expr.index.binding,
        BindingState{Type(Type::Kind::Index), *roles, *index, {}});
  std::vector<Value> results;
  for (auto id : states) {
    const auto &state = bindings.at(id);
    if (!state.value || !available(*state.value))
      return fail("source.move",
                  "loop state needs a wholly available initial value, "
                  "including for zero trips",
                  expr.span);
    if (!std::includes(roles->begin(), roles->end(), state.roles.begin(),
                       state.roles.end()))
      return fail(
          "source.roles",
          "every participant of mutable state must be in the loop roster",
          expr.span);
    if (!use(*state.value, expr.span) ||
        !nested.addInput(id, state.type, state.roles, expr.span))
      return false;
    operation.carried.push_back(*state.value);
    results.push_back({state.type, state.roles, expr.span});
  }
  for (const auto &p : summary->places) {
    if (states.count(p.binding))
      continue;
    auto type = projected(bindings.at(p.binding).type, p.path, expr.span);
    auto caps = type ? checker.types.permissions(*type, expr.span, &decl)
                     : std::nullopt;
    if (!caps)
      return false;
    if (!caps->copy)
      return fail("source.permission",
                  "loop invariants require Copy; declare mutable state and "
                  "supply its successor",
                  expr.span);
    const auto &original = bindings.at(p.binding).roles;
    std::vector<unsigned> selected;
    std::set_intersection(original.begin(), original.end(), roles->begin(),
                          roles->end(), std::back_inserter(selected));
    if (selected.empty())
      return fail("source.roles", "capture has no loop participant", expr.span);
    auto value = capturePlace(p, expr.span);
    if (!value)
      return false;
    value = restrictRoles(*value, selected, expr.span);
    if (!value || !use(*value, expr.span))
      return false;
    ValueId input{uint32_t(region->values.size())};
    if (!importPlace(nested, p, *value, expr.span) ||
        !nested.use(input, expr.span))
      return false;
    operation.captures.push_back(*value);
  }
  std::map<unsigned, ServiceId> roots;
  for (auto id : summary->services) {
    auto root = services.at(id);
    auto found = roots.find(root.index);
    if (found != roots.end()) {
      nested.services.emplace(id, found->second);
      continue;
    }
    auto port = body.services[root.index];
    if (!llvm::is_contained(*roles, port.owner))
      return fail("source.roles", "captured service owner is outside the loop",
                  expr.span);
    if (!nested.addService(id, port))
      return false;
    roots.emplace(root.index, nested.services.at(id));
    operation.services.push_back(root);
  }
  auto tail =
      nested.tail(syntax.bodies[expr.regions.front()], Type(Type::Kind::Unit));
  if (!tail || !nested.discard(*tail, expr.span))
    return false;
  for (auto id : states) {
    const auto &state = nested.bindings.at(id);
    if (!state.value || !nested.available(*state.value))
      return fail(
          "source.move",
          "loop state needs a whole successor on every continuing iteration",
          expr.span);
    if (!nested.use(*state.value, expr.span))
      return false;
    region->results.push_back(*state.value);
  }
  if (!nested.finish(expr.span))
    return false;
  body.mayStop |= region->mayStop;
  body.opaque |= region->opaque;
  operation.region = region;
  auto emitted =
      emitResults(std::move(operation), std::move(results), expr.span);
  if (!emitted)
    return false;
  unsigned i = 0;
  for (auto id : states) {
    bindings.at(id).value = (*emitted)[i++];
    bindings.at(id).pieces.clear();
  }
  return true;
}
} // namespace zkc::language::detail
