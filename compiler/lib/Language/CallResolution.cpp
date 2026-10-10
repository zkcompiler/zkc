#include "BodyCheck.h"
using namespace llvm;
namespace zkc::language::detail {
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
      auto component = type(decl, term);
      if (!component)
        return {};
      auto &interface = output.declarations[parameter.interface->index];
      for (auto id : interface.members)
        if (output.declarations[id.index].name == parts.second)
          return CallableReference{id, *component};
      types.fail("source.call", "unknown interface member", span);
      return {};
    }
  // A bound component member takes precedence over a nominal alternative.
  auto alternative = name.rsplit("::");
  if (!alternative.second.empty()) {
    auto nominal = resolve(decl, alternative.first, span, false);
    if (nominal &&
        output.declarations[nominal->index].kind == Declaration::Kind::Variant)
      return CallableReference{*nominal, {}};
  }
  auto id = resolve(decl, name, span);
  if (!id)
    return {};
  if (output.declarations[id->index].abstract &&
      output.declarations[id->index].kind != Declaration::Kind::Associated) {
    types.fail("source.call", "abstract call requires a bound component", span);
    return {};
  }
  return CallableReference{*id, {}};
}
std::optional<ExpressionTypes::Callable>
BodyChecker::callable(const Expression &expr) {
  return checker.callable(decl, expr.text, expr.span);
}
} // namespace zkc::language::detail
