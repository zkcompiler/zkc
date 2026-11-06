#include "BodyCheck.h"
#include "BodySummary.h"
#include "ScopedWitness.h"
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
  case K::Subscript:
    if (!inference->callees.count(id))
      break;
    [[fallthrough]];
  case K::NotationCall:
  case K::MethodCall:
  case K::Call: {
    // index<N>() is a checked built-in mathematical constant, not a
    // declaration in the inferred callee map. Ordinary expression checking
    // still validates its static natural and exact empty argument list.
    if (expr.kind == K::Call && !expr.binding && expr.text == "index")
      break;
    if (expr.binding) {
      auto binding = scoped.find(*expr.binding);
      if (binding == scoped.end() ||
          body.scopedBindings[binding->second].signature.mode !=
              ScopedSignature::Mode::Math)
        return refuse();
      break;
    }
    auto callee = inference->callees.find(id);
    if (callee == inference->callees.end())
      return refuse();
    const auto &target =
        checker.output.declarations[callee->second.declaration.index];
    if (target.kind != Declaration::Kind::Math &&
        target.kind != Declaration::Kind::Variant &&
        !(target.kind == Declaration::Kind::View &&
          (!target.descriptorResult || inference->descriptorTypes.count(id))) &&
        !(target.kind == Declaration::Kind::InstalledViewScheme &&
          inference->descriptorTypes.count(id)))
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
  case K::If:
  case K::Match:
    break;
  case K::DomainProduct:
    if (!inference->descriptorTypes.count(id))
      return refuse();
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
  if (!protocol())
    return control(expr, Type{}, depth, false);
  const auto id = uint32_t(&expr - syntax.expressions.data());
  if (!mathematicalExpression(id, depth))
    return {};
  ScopedSignature signature;
  signature.mode = ScopedSignature::Mode::Math;
  signature.result = Type{};
  auto index = scopedComputation(id, signature, depth);
  if (!index)
    return {};
  // Only free-place snapshots are formed here. The original selected expression
  // executes in the Math body, including every nested RHS computation.
  auto binding =
      summarizeScopedBinding(checker.types, body, *index, {}, {}, {}, 1, true);
  if (!binding)
    return {};
  auto summary = checker.bodySummaries.apply(
      checker.types, checker.output.declarations, *binding->computation->body,
      binding->statics, binding->captures, binding->scoped, 1, binding->domains,
      binding->lexical, callDepth + 1, binding->owner);
  if (!summary || summary->results.size() != 1)
    return {};
  if (callDepth > checker.work.limits.callDepth ||
      summary->callHeight > checker.work.limits.callDepth - callDepth) {
    fail("source.limit", "retained Boolean call depth exceeded", expr.span);
    return {};
  }
  auto apply =
      [&](const Dependencies &dependency) -> std::optional<Components> {
    if (dependency.parameterized) {
      fail("source.scoped-summary", "Boolean placement needs total mathematics",
           expr.span);
      return {};
    }
    std::vector<ValueId> operands;
    for (auto input : dependency.inputs)
      operands.push_back({input});
    return combine(operands, expr.span);
  };
  for (const auto &formation : summary->formation)
    if (!apply(formation))
      return {};
  auto available = apply(summary->results.front());
  if (!available)
    return {};
  if (!checker.types.charge(1, expr.span))
    return {};
  const auto source = uint32_t(witnesses.invocations.size());
  witnesses.invocations.push_back(std::make_shared<ScopedInvocationSource>(
      ScopedInvocationSource{decl.id, id, {}}));
  checker.bodyHeights[decl.id.index] =
      std::max(checker.bodyHeights[decl.id.index],
               summary->callHeight + lexicalCallbackDepth + 1);
  return emit(ScopedInvoke{*index, {}, source}, Type{}, *available, expr.span);
}
} // namespace zkc::language::detail
