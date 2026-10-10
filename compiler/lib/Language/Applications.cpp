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
  const auto id = uint32_t(&expr - syntax.expressions.data());
  TypeScope types(*this, id, {});
  if (!types)
    return {};
  const auto &target = inference->callees.at(id);
  auto &callee = checker.output.declarations[target.declaration.index];
  if (callee.kind != Declaration::Kind::Protocol) {
    fail("source.call", "application target must be a protocol", expr.span);
    return {};
  }
  if (callee.completes) {
    fail("source.completion",
         "a completing protocol can only be selected as an Entry", expr.span);
    return {};
  }
  if (expr.children.size() != callee.inputOrder.size()) {
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
  const auto &binding = inference->inputs.at(id);
  const auto &arguments = inference->arguments.at(id);
  auto substitution = checker.types.substitution(callee, arguments);
  std::vector<ValueId> operands(callee.inputs.size());
  std::vector<ServiceId> managed(callee.services.size());
  // Evaluate authored operands in source order; inputOrder identifies the
  // destination independently of that order, including managed services.
  for (unsigned i = 0; i < expr.children.size(); ++i) {
    auto child = expr.children[i];
    const auto &slot = callee.inputOrder[binding[i]];
    if (slot.kind == Declaration::InputSlot::Kind::Service) {
      auto root = service(syntax.expressions[child]);
      if (!root)
        return {};
      const auto &actual = body.services[root->index];
      const auto &expected = callee.services[slot.index];
      auto field =
          checker.types.substitute(expected.field, substitution, expr.span);
      if (!field)
        return {};
      if (*field != actual.field || mapping[expected.owner] != actual.owner) {
        fail("source.service", "managed service field or mapped owner differs",
             expr.span);
        return {};
      }
      managed[slot.index] = *root;
    } else {
      const auto &port = callee.inputs[slot.index];
      auto type = checker.types.substitute(port.type, substitution, expr.span);
      if (!type)
        return {};
      auto value = expression(child, *type);
      if (!value || !demand(*value, mappedRoles(port), expr.span) ||
          !use(*value, expr.span))
        return {};
      operands[slot.index] = *value;
    }
  }
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
      ProtocolApplication{callee.id, operands, arguments, mapping, managed},
      std::move(results), expr.span);
  if (emitted)
    placement->applications.push_back(body.operations.size() - 1);
  return emitted;
}
} // namespace zkc::language::detail
