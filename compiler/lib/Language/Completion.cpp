#include "BodyCheck.h"
using namespace llvm;
namespace zkc::language::detail {
std::optional<std::vector<ValueId>>
BodyChecker::complete(const Statement &statement) {
  const auto &expr = syntax.expressions[statement.expression];
  if (!protocol() || statement.kind != Statement::Kind::Let ||
      statement.owner || statement.roles || statement.type ||
      statement.exchange || statement.mutableBinding) {
    fail("source.mode",
         "finish_if requires an unannotated protocol let binding",
         statement.span);
    return {};
  }
  if (!decl.completes) {
    fail("source.completion", "finish_if requires a completes declaration",
         expr.span);
    return {};
  }
  auto role = checker.roles(decl, {expr.text}, expr.span);
  if (!role || !active(*role, expr.span))
    return {};
  unsigned owner = role->front();
  auto condition = expression(expr.children.front(), Type{});
  if (!condition || !use(*condition, expr.span))
    return {};
  if (!demand(*condition, {owner}, expr.span))
    return {};
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
    if (found == ports.end() || !seen.insert(found->second).second) {
      fail("source.completion", "unknown or repeated completion output",
           expr.span);
      return {};
    }
    const auto &port = *outputs[found->second];
    auto value = expression(expr.children[i + 1], port.type);
    if (!value)
      return {};
    if (!demand(*value, {owner}, expr.span))
      return {};
    if (!use(*value, expr.span))
      return {};
    operation.values[found->second] = *value;
  }
  if (seen.size() != outputs.size()) {
    fail("source.completion", "completion must supply every owner output",
         expr.span);
    return {};
  }
  std::vector<Value> results;
  for (unsigned i = 0; i < outputs.size(); ++i) {
    auto caps = checker.types.permissions(outputs[i]->type, expr.span, &decl);
    if (!caps)
      return {};
    auto available = components(operation.values[i]);
    if (available.owners.empty() && available.roles != *role && !caps->drop) {
      fail("source.permission",
           "completion cannot discard components without Drop", expr.span);
      return {};
    }
    if (!caps->copy) {
      operation.continuations.push_back(i);
      results.push_back({outputs[i]->type, *role, expr.span});
    }
  }
  auto emitted =
      emitResults(std::move(operation), std::move(results), expr.span);
  return emitted;
}
} // namespace zkc::language::detail
