#include "BodyCheck.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
bool BodyChecker::repeat(const Statement &statement) {
  const auto &expr = syntax.expressions[statement.expression];
  if (!protocol() || statement.kind != Statement::Kind::Let ||
      statement.owner || statement.roles || statement.type ||
      statement.exchange)
    return fail("source.mode",
                "protocol repeat requires an unannotated let binding",
                statement.span);
  auto roles = checker.roles(decl, *expr.roles, expr.span);
  if (!roles || !active(*roles, expr.span))
    return false;
  const auto names =
      statement.resultNames.value_or(std::vector<std::string>{statement.name});
  if (names.size() != expr.labels.size())
    return fail("source.binding", "repeat result count must match carry",
                expr.span);
  std::set<std::string> seen;
  for (const auto &name : names)
    if (!checker.bindingName(decl, name, statement.span) ||
        bindings.count(name) || services.count(name) ||
        !seen.insert(name).second)
      return checker.diagnostic
                 ? false
                 : fail("source.shadow", "repeat result shadows a binding",
                        statement.span);
  auto maximum = checker.type(decl, expr.arguments.front());
  if (!maximum)
    return false;
  if (maximum->kind != Type::Kind::Natural)
    return fail("source.bound", "repeat maximum must be a static natural",
                expr.span);
  if (maximum->dimension.isClosed() &&
      maximum->dimension.closedValue() > 1048576)
    return fail("source.bound", "repeat maximum exceeds installed limit",
                expr.span);
  auto count = expression(expr.children.front(), Type(Type::Kind::Index));
  if (!count || !use(*count, expr.span))
    return false;
  const auto &countRoles = body.values[count->index].components;
  if (!std::includes(countRoles.begin(), countRoles.end(), roles->begin(),
                     roles->end()))
    return fail("source.roles",
                "repeat count must be available at every loop participant",
                expr.span);
  ProtocolRepeat operation{*roles, *count, maximum->dimension, {}, {}, {}, {}};
  auto region = std::make_shared<Body>();
  region->mode = Body::Mode::Protocol;
  BodyChecker nested(checker, decl, syntax, *region, callDepth);
  nested.activeRoles = *roles;
  if (!nested.addInput(expr.text, Type(Type::Kind::Index), *roles, expr.span))
    return false;
  std::vector<Port> outputs;
  std::vector<Value> results;
  for (unsigned i = 0; i < expr.labels.size(); ++i) {
    auto value = expression(expr.children[i + 1]);
    if (!value || !use(*value, expr.span))
      return false;
    const auto &initial = body.values[value->index];
    if (!checker.executableType(initial.type, expr.span))
      return false;
    auto caps = checker.permissions(initial.type, expr.span, &decl);
    if (!caps)
      return false;
    std::vector<unsigned> carriedRoles;
    if (expr.carriedRoles[i]) {
      auto specified = checker.roles(decl, *expr.carriedRoles[i], expr.span);
      if (!specified)
        return false;
      carriedRoles = *specified;
    } else
      std::set_intersection(initial.components.begin(),
                            initial.components.end(), roles->begin(),
                            roles->end(), std::back_inserter(carriedRoles));
    if (carriedRoles.empty() ||
        !std::includes(roles->begin(), roles->end(), carriedRoles.begin(),
                       carriedRoles.end()) ||
        !std::includes(initial.components.begin(), initial.components.end(),
                       carriedRoles.begin(), carriedRoles.end()))
      return fail("source.roles",
                  "carried value is unavailable at its declared loop roles",
                  expr.span);
    if ((carriedRoles != initial.components && !caps->drop) ||
        (carriedRoles.size() > 1 &&
         (!caps->copy || !caps->drop || !caps->share)))
      return fail("source.permission",
                  "carried roles exceed the value's permissions", expr.span);
    operation.carried.push_back(*value);
    if (!nested.addInput(expr.labels[i], initial.type, carriedRoles, expr.span))
      return false;
    outputs.push_back({expr.labels[i], initial.type, carriedRoles, expr.span});
    results.push_back({initial.type, carriedRoles, expr.span});
  }
  for (const auto &name : expr.captures) {
    auto found = bindings.find(name);
    if (found == bindings.end())
      return fail("source.name", "unknown data capture: " + name, expr.span);
    auto value = found->second;
    const auto &captured = body.values[value.index];
    if (!checker.executableType(captured.type, expr.span))
      return false;
    auto caps = checker.permissions(captured.type, expr.span, &decl);
    if (!caps)
      return false;
    if (!caps->copy)
      return fail("source.permission",
                  "repeat captures require Copy; carry affine values",
                  expr.span);
    std::vector<unsigned> available;
    std::set_intersection(captured.components.begin(),
                          captured.components.end(), roles->begin(),
                          roles->end(), std::back_inserter(available));
    if (available.empty())
      return fail("source.roles", "capture has no loop participant", expr.span);
    if (available != captured.components && !caps->drop)
      return fail("source.permission",
                  "capture cannot discard components without Drop", expr.span);
    if (!use(value, expr.span))
      return false;
    ValueId input{uint32_t(region->values.size())};
    if (!nested.addInput(name, captured.type, available, expr.span) ||
        !nested.use(input, expr.span))
      return false;
    operation.captures.push_back(value);
  }
  for (const auto &name : expr.services) {
    auto found = services.find(name);
    if (found == services.end())
      return fail("source.service", "unknown managed capture: " + name,
                  expr.span);
    auto port = body.services[found->second.index];
    port.name = name;
    if (!llvm::is_contained(*roles, port.owner))
      return fail("source.roles", "captured service owner is outside the loop",
                  expr.span);
    if (!nested.addService(port))
      return false;
    operation.services.push_back(found->second);
  }
  if (!nested.run(syntax.bodies[expr.regions.front()], outputs, true))
    return false;
  body.mayStop |= region->mayStop;
  body.opaque |= region->opaque;
  operation.region = region;
  auto emitted =
      emitResults(std::move(operation), std::move(results), expr.span);
  if (!emitted)
    return false;
  for (unsigned i = 0; i < names.size(); ++i)
    bindings.emplace(names[i], (*emitted)[i]);
  return true;
}
} // namespace zkc::language::detail
