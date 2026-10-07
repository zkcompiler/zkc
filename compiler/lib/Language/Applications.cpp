#include "BodyCheck.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
bool BodyChecker::application(const Statement &statement) {
  const auto &expr = syntax.expressions[statement.expression];
  if (!protocol() || statement.kind != Statement::Kind::Let ||
      statement.owner || statement.roles || statement.type ||
      statement.exchange)
    return fail(
        "source.mode",
        "protocol application requires an unannotated protocol let binding",
        statement.span);
  auto target = checker.resolve(decl, expr.text, expr.span);
  if (!target)
    return false;
  auto &callee = checker.output.declarations[target->index];
  if (callee.kind != Declaration::Kind::Protocol)
    return fail("source.call", "application target must be a protocol",
                expr.span);
  const auto names =
      statement.resultNames.value_or(std::vector<std::string>{statement.name});
  if (names.size() != callee.outputs.size() ||
      expr.children.size() != callee.inputs.size())
    return fail("source.call",
                "protocol application input or result count differs",
                expr.span);
  std::set<std::string> seen;
  for (const auto &name : names)
    if (!checker.bindingName(decl, name, statement.span) ||
        bindings.count(name) || !seen.insert(name).second)
      return checker.diagnostic ? false
                                : fail("source.shadow",
                                       "duplicate or shadowing result binding",
                                       statement.span);
  const auto &roleNames = expr.roles ? *expr.roles : callee.roles;
  if (roleNames.size() != callee.roles.size())
    return fail("source.roles",
                "protocol role substitution must cover the callee roster",
                expr.span);
  std::vector<unsigned> mapping;
  for (const auto &name : roleNames) {
    auto role = checker.roles(decl, {name}, expr.span);
    if (!role)
      return false;
    if (llvm::is_contained(mapping, role->front()))
      return fail("source.roles",
                  "protocol role substitution must be injective", expr.span);
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
    if (checker.diagnostic)
      return false;
  }
  auto arguments = actuals(callee, expr, hints, {}, {});
  if (!arguments)
    return false;
  auto substitution = checker.substitution(callee, *arguments);
  std::vector<ValueId> operands;
  for (unsigned i = 0; i < expr.children.size(); ++i) {
    const auto &port = callee.inputs[i];
    auto type = checker.substitute(port.type, substitution, expr.span);
    if (!type)
      return false;
    auto value = expression(expr.children[i], *type);
    if (!value)
      return false;
    auto roles = mappedRoles(port);
    const auto &available = body.values[value->index].components;
    if (!std::includes(available.begin(), available.end(), roles.begin(),
                       roles.end()))
      return fail("source.roles",
                  "protocol argument lacks a required participant component",
                  expr.span);
    auto permissions = checker.permissions(*type, expr.span, &decl);
    if (!permissions || (available != roles && !permissions->drop))
      return checker.diagnostic
                 ? false
                 : fail("source.permission",
                        "application cannot discard a component without Drop",
                        expr.span);
    if (!use(*value, expr.span))
      return false;
    operands.push_back(*value);
  }
  if (!checker.body(callee.id, callDepth + 1))
    return false;
  checker.bodyHeights[decl.id.index] =
      std::max(checker.bodyHeights[decl.id.index],
               checker.bodyHeights[callee.id.index] + 1);
  body.mayStop |= callee.body->mayStop;
  body.opaque |= callee.body->opaque;
  std::vector<Value> results;
  for (const auto &port : callee.outputs) {
    auto type = checker.substitute(port.type, substitution, expr.span);
    if (!type)
      return false;
    results.push_back({*type, mappedRoles(port), expr.span});
  }
  auto emitted =
      emitResults(ProtocolApplication{callee.id, operands, *arguments, mapping},
                  std::move(results), expr.span);
  if (!emitted)
    return false;
  for (unsigned i = 0; i < names.size(); ++i)
    bindings.emplace(names[i], (*emitted)[i]);
  return true;
}
} // namespace zkc::language::detail
