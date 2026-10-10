#include "Checker.h"
using namespace llvm;
namespace zkc::language::detail {
/// Expand control notation before lexical resolution. Generated branch tails
/// remain part of the enclosing expression's inference problem; no synthetic
/// let statement creates an extra inference boundary.
bool elaborateExpressions(Checker &checker, SyntaxDeclaration &syntax) {
  if (syntax.elaborated)
    return true;
  using K = Expression::Kind;
  const auto count = syntax.expressions.size();
  for (unsigned i = 0; i < count; ++i) {
    auto kind = syntax.expressions[i].kind;
    if (kind != K::Not && (syntax.kind != Declaration::Kind::Local ||
                           (kind != K::And && kind != K::Or)))
      continue;
    auto expression = syntax.expressions[i];
    expression.notation.reset();
    if (!checker.types.charge(4, expression.span))
      return false;
    Expression literal;
    literal.kind = K::Boolean;
    literal.text = kind == K::Or ? "true" : "false";
    literal.span = expression.span;
    const auto constant = uint32_t(syntax.expressions.size());
    syntax.expressions.push_back(std::move(literal));
    if (kind == K::Not) {
      expression.kind = K::Call;
      expression.text = "::zkc::prelude::boolean_equal";
      expression.children.push_back(constant);
    } else {
      const auto right = expression.children[1];
      expression.kind = K::If;
      expression.children.resize(1);
      for (auto value : kind == K::And
                            ? std::vector<uint32_t>{right, constant}
                            : std::vector<uint32_t>{constant, right}) {
        SyntaxBody arm;
        arm.region = true;
        arm.span = expression.span;
        arm.results.emplace_back("", value);
        expression.regions.push_back(syntax.bodies.size());
        syntax.bodies.push_back(std::move(arm));
      }
    }
    syntax.expressions[i] = std::move(expression);
  }
  syntax.elaborated = true;
  return true;
}
} // namespace zkc::language::detail
