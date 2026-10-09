#include "BodyCheck.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
std::optional<std::vector<ValueId>>
BodyChecker::application(const Expression &expr) {
  if (!protocol()) {
    fail("source.mode", "protocol application requires protocol mode",
         expr.span);
    return {};
  }
  auto target = checker.resolve(decl, expr.text, expr.span);
  if (!target)
    return {};
  auto &callee = checker.output.declarations[target->index];
  if (callee.kind != Declaration::Kind::Protocol) {
    fail("source.call", "application target must be a protocol", expr.span);
    return {};
  }
  if (callee.completes) {
    fail("source.completion",
         "a completing protocol can only be selected as an Entry", expr.span);
    return {};
  }
  if (expr.children.size() != callee.inputs.size()) {
    fail("source.call", "protocol application input count differs", expr.span);
    return {};
  }
  const auto &roleNames = expr.roles ? *expr.roles : callee.roles;
  if (roleNames.size() != callee.roles.size()) {
    fail("source.roles",
         "protocol role substitution must cover the callee roster", expr.span);
    return {};
  }
  std::vector<unsigned> mapping;
  for (const auto &name : roleNames) {
    auto role = checker.roles(decl, {name}, expr.span);
    if (!role)
      return {};
    if (llvm::is_contained(mapping, role->front())) {
      fail("source.roles", "protocol role substitution must be injective",
           expr.span);
      return {};
    }
    if (!active(*role, expr.span))
      return {};
    mapping.push_back(role->front());
  }
  auto mappedRoles = [&](const Port &port) {
    std::vector<unsigned> roles;
    for (auto role : port.roles)
      roles.push_back(mapping[role]);
    llvm::sort(roles);
    return roles;
  };
  std::vector<std::optional<Type>> hints;
  for (auto child : expr.children) {
    hints.push_back(hint(child));
    if (checker.types.diagnostic)
      return {};
  }
  auto arguments = actuals(callee, expr, hints, {}, {});
  if (!arguments)
    return {};
  auto substitution = checker.types.substitution(callee, *arguments);
  if (expr.services.size() != callee.services.size()) {
    fail("source.service", "protocol application managed port count differs",
         expr.span);
    return {};
  }
  std::vector<ServiceId> managed;
  for (unsigned i = 0; i < expr.services.size(); ++i) {
    auto found = services.find(expr.serviceBindings[i]);
    if (found == services.end()) {
      fail("source.service", "application requires an existing managed binding",
           expr.span);
      return {};
    }
    const auto &actual = body.services[found->second.index];
    const auto &expected = callee.services[i];
    auto field =
        checker.types.substitute(expected.field, substitution, expr.span);
    if (!field)
      return {};
    if (*field != actual.field || mapping[expected.owner] != actual.owner) {
      fail("source.service", "managed service field or mapped owner differs",
           expr.span);
      return {};
    }
    managed.push_back(found->second);
  }
  std::vector<ValueId> operands;
  for (unsigned i = 0; i < expr.children.size(); ++i) {
    const auto &port = callee.inputs[i];
    auto type = checker.types.substitute(port.type, substitution, expr.span);
    if (!type)
      return {};
    auto value = expression(expr.children[i], *type);
    if (!value)
      return {};
    auto roles = mappedRoles(port);
    const auto &available = body.values[value->index].components;
    if (!std::includes(available.begin(), available.end(), roles.begin(),
                       roles.end())) {
      fail("source.roles",
           "protocol argument lacks a required participant component",
           expr.span);
      return {};
    }
    auto permissions = checker.types.permissions(*type, expr.span, &decl);
    if (!permissions)
      return {};
    if (available != roles && !permissions->drop) {
      fail("source.permission",
           "application cannot discard a component without Drop", expr.span);
      return {};
    }
    if (!use(*value, expr.span))
      return {};
    operands.push_back(*value);
  }
  if (!checker.body(callee.id, callDepth + 1))
    return {};
  checker.bodyHeights[decl.id.index] =
      std::max(checker.bodyHeights[decl.id.index],
               checker.bodyHeights[callee.id.index] + 1);
  body.mayStop |= callee.body->mayStop;
  body.opaque |= callee.body->opaque;
  std::vector<Value> results;
  for (const auto &port : callee.outputs) {
    auto type = checker.types.substitute(port.type, substitution, expr.span);
    if (!type)
      return {};
    results.push_back({*type, mappedRoles(port), expr.span});
  }
  auto emitted = emitResults(
      ProtocolApplication{callee.id, operands, *arguments, mapping, managed},
      std::move(results), expr.span);
  return emitted;
}
} // namespace zkc::language::detail
