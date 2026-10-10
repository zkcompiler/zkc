#include "BodyCheck.h"
using namespace llvm;
namespace zkc::language::detail {
bool BodyChecker::mathematicalExpression(uint32_t id, unsigned depth) {
  if (mathematicalExpressions.count(id))
    return true;
  const auto &expr = syntax.expressions[id];
  if (depth > checker.work.limits.expressionDepth ||
      !checker.types.charge(1, expr.span))
    return checker.types.diagnostic
               ? false
               : fail("source.limit", "mathematical operand depth exceeded",
                      expr.span);
  auto refuse = [&] {
    return fail("source.mode",
                "protocol Boolean operands require total mathematics; "
                "put conditional execution in a local fn",
                expr.span);
  };
  using K = Expression::Kind;
  switch (expr.kind) {
  case K::NotationCall:
  case K::Call: {
    if (expr.binding) {
      auto binding = scoped.find(*expr.binding);
      if (binding == scoped.end() ||
          body.scopedBindings[binding->second].signature.mode !=
              ScopedSignature::Mode::Math)
        return refuse();
      break;
    }
    auto callee = inference->callees.find(id);
    if (callee == inference->callees.end() ||
        checker.output.declarations[callee->second.declaration.index].kind !=
            Declaration::Kind::Math)
      return refuse();
    break;
  }
  case K::Lambda: {
    auto signature = inference->scopedSignatures.find(id);
    // Deferred code is checked by the ordinary Body checker in its declared
    // mode. It is not an eagerly evaluated Boolean operand.
    return signature != inference->scopedSignatures.end() &&
                   signature->second.mode == ScopedSignature::Mode::Math
               ? true
               : refuse();
  }
  case K::Name:
  case K::Decimal:
  case K::Boolean:
  case K::And:
  case K::Or:
  case K::Tuple:
  case K::Array:
  case K::Record:
  case K::Projection:
  case K::Block:
    break;
  default:
    return refuse();
  }
  for (auto child : expr.children)
    if (!mathematicalExpression(child, depth + 1))
      return false;
  for (auto region : expr.regions) {
    const auto &source = syntax.bodies[region];
    if (source.stopped)
      return refuse();
    for (const auto &statement : source.statements) {
      if ((statement.kind != Statement::Kind::Let &&
           statement.kind != Statement::Kind::Expression) ||
          statement.mutableBinding || statement.exchange)
        return refuse();
      if (!mathematicalExpression(statement.expression, depth + 1))
        return false;
    }
    for (const auto &[name, value] : source.results)
      if (!mathematicalExpression(value, depth + 1))
        return false;
  }
  mathematicalExpressions.insert(id);
  return true;
}
std::optional<ValueId> BodyChecker::boolean(const Expression &expr,
                                            unsigned depth) {
  if (local())
    return control(expr, Type{}, depth, false);
  std::vector<ValueId> operands;
  for (auto child : expr.children) {
    if (protocol() && !mathematicalExpression(child, depth + 1))
      return {};
    auto value = expression(child, Type{}, depth + 1);
    if (!value || !use(*value, expr.span))
      return {};
    operands.push_back(*value);
  }
  auto available = combine(operands, expr.span);
  if (!available)
    return {};
  return emit(MathValue{expr.kind == Expression::Kind::And
                            ? MathematicalIdentity::BooleanAnd
                            : MathematicalIdentity::BooleanOr,
                        std::move(operands),
                        {}},
              Type{}, *available, expr.span);
}
} // namespace zkc::language::detail
