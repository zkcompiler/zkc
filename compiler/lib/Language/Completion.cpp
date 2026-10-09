#include "BodyCheck.h"
using namespace llvm;
namespace zkc::language::detail {
bool BodyChecker::complete(const Statement &statement) {
  const auto &expr = syntax.expressions[statement.expression];
  if (!protocol() || statement.kind != Statement::Kind::Let ||
      statement.owner || statement.roles || statement.type ||
      statement.exchange)
    return fail("source.mode",
                "finish_if requires an unannotated protocol let binding",
                statement.span);
  if (!decl.completes)
    return fail("source.completion",
                "finish_if requires a completes declaration", expr.span);
  auto role = checker.roles(decl, {expr.text}, expr.span);
  if (!role || !active(*role, expr.span))
    return false;
  unsigned owner = role->front();
  auto condition = expression(expr.children.front(), Type{});
  if (!condition || !use(*condition, expr.span))
    return false;
  if (!is_contained(body.values[condition->index].components, owner))
    return fail("source.roles",
                "completion condition is unavailable at its owner", expr.span);
  std::vector<const Port *> outputs;
  std::map<std::string, unsigned> ports;
  for (const auto &port : decl.outputs)
    if (is_contained(port.roles, owner)) {
      ports.emplace(port.name, outputs.size());
      outputs.push_back(&port);
    }
  ProtocolCompletion operation{
      *condition, owner, std::vector<ValueId>(outputs.size()), {}};
  std::set<unsigned> seen;
  for (unsigned i = 0; i < expr.labels.size(); ++i) {
    auto found = ports.find(expr.labels[i]);
    if (found == ports.end() || !seen.insert(found->second).second)
      return fail("source.completion", "unknown or repeated completion output",
                  expr.span);
    const auto &port = *outputs[found->second];
    auto value = expression(expr.children[i + 1], port.type);
    if (!value)
      return false;
    if (!is_contained(body.values[value->index].components, owner))
      return fail("source.roles",
                  "completion result is unavailable at its owner", expr.span);
    if (!use(*value, expr.span))
      return false;
    operation.values[found->second] = *value;
  }
  if (seen.size() != outputs.size())
    return fail("source.completion",
                "completion must supply every owner output", expr.span);
  std::vector<Value> results;
  for (unsigned i = 0; i < outputs.size(); ++i) {
    auto caps = checker.types.permissions(outputs[i]->type, expr.span, &decl);
    if (!caps)
      return false;
    if (!caps->copy) {
      operation.continuations.push_back(i);
      results.push_back({outputs[i]->type, *role, expr.span});
    }
  }
  const auto names =
      statement.resultNames.value_or(std::vector<std::string>{statement.name});
  if (names.size() != results.size())
    return fail("source.binding",
                "finish_if binds non-Copy outputs in declaration order",
                expr.span);
  std::set<std::string> unique;
  for (const auto &name : names)
    if (!checker.bindingName(decl, name, statement.span) ||
        bindings.count(name) || services.count(name) ||
        !unique.insert(name).second)
      return checker.types.diagnostic
                 ? false
                 : fail("source.shadow", "completion result shadows a binding",
                        statement.span);
  auto emitted =
      emitResults(std::move(operation), std::move(results), expr.span);
  if (!emitted)
    return false;
  for (unsigned i = 0; i < names.size(); ++i)
    bindings.emplace(names[i], (*emitted)[i]);
  return true;
}
} // namespace zkc::language::detail
