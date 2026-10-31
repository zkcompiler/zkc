#include "BindingWitness.h"
#include "BodyCheck.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
std::optional<ValueId> BodyChecker::instantiateOracle(const Expression &expr,
                                                      unsigned depth) {
  const auto id = uint32_t(&expr - syntax.expressions.data());
  if (!protocol() || orderedRoot != id) {
    fail("source.oracle-construction",
         "oracle construction requires an outer '<-' in Protocol mode",
         expr.span);
    return {};
  }
  const auto &target = inference->callees.at(id);
  const auto &callee = checker.output.declarations[target.declaration.index];
  const auto &arguments = inference->arguments.at(id);
  const auto &order = inference->inputs.at(id);
  if (!callee.oracleDefinition || order.size() != expr.children.size() ||
      !checkCallInputMapping(checker.types, order, callee.inputs.size(),
                             expr.span))
    return {};
  auto substitution = checker.types.substitution(callee, arguments);
  if (target.module && callee.parent)
    substitution.emplace(
        "self:" +
            checker.output.declarations[callee.parent->index].qualifiedName,
        *target.module);
  std::vector<ValueId> operands(callee.inputs.size());
  // Evaluate in written order, then bind to canonical constructor slots.
  for (unsigned i = 0; i < expr.children.size(); ++i) {
    auto expected = checker.types.substitute(callee.inputs[order[i]].type,
                                             substitution, expr.span);
    if (!expected)
      return {};
    auto value = expression(expr.children[i], *expected, depth + 1);
    if (!value || !use(*value, expr.span))
      return {};
    operands[order[i]] = *value;
  }
  const auto &first = body.values[operands.front().index];
  auto family = components(operands.front());
  if (!first.oracleHolder || !family.owners.empty() ||
      family.roles.size() < 2 ||
      !llvm::is_contained(family.roles, *first.oracleHolder)) {
    fail("source.oracle-role",
         "constructor source has no complete custody family", expr.span);
    return {};
  }
  const auto holder = *first.oracleHolder;
  for (unsigned i = 0; i < callee.oracleDefinition->sourceCount; ++i) {
    const auto &source = body.values[operands[i].index];
    auto available = components(operands[i]);
    if (source.oracleHolder != holder || !available.owners.empty() ||
        available.roles != family.roles) {
      fail("source.oracle-role",
           "constructor sources have different custody families", expr.span);
      return {};
    }
  }
  if (!active(family.roles, expr.span))
    return {};
  for (unsigned i = callee.oracleDefinition->sourceCount; i < operands.size();
       ++i)
    if (!demand(operands[i], family.roles, expr.span))
      return {};
  auto resultType = checker.types.substitute(callee.outputs.front().type,
                                             substitution, expr.span);
  if (!resultType)
    return {};
  auto receivers = family.roles;
  llvm::erase(receivers, holder);
  auto result = emit(OracleInstantiation{callee.id, arguments, target.module,
                                         operands, holder, receivers},
                     *resultType, family, expr.span);
  if (!result)
    return {};
  auto &operation = body.operations.back();
  operation.binding = CallBinding{target, arguments, operands, {}, {}, {}, {}};
  operation.binding->argumentOrder = order;
  placement->oracleInstantiations.push_back(body.operations.size() - 1);
  return result;
}
} // namespace zkc::language::detail
