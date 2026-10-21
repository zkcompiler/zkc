#include "BodyCheck.h"
#include "zkc/Language/Diagnostics.h"
using namespace llvm;
namespace zkc::language::detail {
bool Checker::domainExpression(const Declaration &decl,
                               const SyntaxDeclaration &syntax, uint32_t id) {
  const auto &expr = syntax.expressions[id];
  if (expr.kind == Expression::Kind::Name && expr.binding)
    return syntax.bindings[expr.binding->index].domain;
  if (expr.kind != Expression::Kind::Call || expr.binding ||
      expr.text == "index" || expr.text == "unpack")
    return false;
  auto target = callable(decl, expr.text, expr.span);
  return target && output.declarations[target->declaration.index].kind ==
                       Declaration::Kind::DomainFunction;
}
std::optional<CallableReference> Checker::callable(const Declaration &decl,
                                                   StringRef name, Span span) {
  auto parts = name.split("::");
  if (!parts.second.empty())
    for (auto &parameter : decl.parameters) {
      if (parameter.name != parts.first || !parameter.interface)
        continue;
      SyntaxType term;
      term.name = parameter.name;
      term.span = span;
      auto module = type(decl, term);
      if (!module)
        return {};
      auto &interface = output.declarations[parameter.interface->index];
      for (auto id : interface.members)
        if (output.declarations[id.index].name == parts.second) {
          if (!signature(id))
            return {};
          if (!recordReference(decl,
                               moduleParameterProviders.at(parameter.atom), id,
                               name, span, formatType(*module)))
            return {};
          return CallableReference{id, *module};
        }
      types.fail("source.call", "unknown interface member", span);
      return {};
    }
  // A bound module member takes precedence over a nominal alternative.
  auto alternative = name.rsplit("::");
  if (!alternative.second.empty()) {
    auto nominal = resolve(decl, alternative.first, span, false);
    if (nominal &&
        output.declarations[nominal->index].kind == Declaration::Kind::Variant)
      return CallableReference{*nominal, {}};
  }
  auto id = resolve(decl, name, span);
  if (!id || !signature(*id))
    return {};
  if (output.declarations[id->index].abstract &&
      output.declarations[id->index].kind != Declaration::Kind::Associated) {
    types.fail("source.call", "abstract call requires a bound module", span);
    return {};
  }
  return CallableReference{*id, {}};
}
std::optional<ExpressionTypes::Callable>
BodyChecker::callable(const Expression &expr) {
  return checker.callable(decl, expr.text, expr.span);
}
} // namespace zkc::language::detail
