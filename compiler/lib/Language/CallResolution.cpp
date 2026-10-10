#include "BodyCheck.h"
using namespace llvm;
namespace zkc::language::detail {
std::optional<ExpressionTypes::Callable>
BodyChecker::callable(const Expression &expr) {
  auto parts = StringRef(expr.text).split("::");
  if (!parts.second.empty())
    for (auto &parameter : decl.parameters) {
      if (parameter.name != parts.first || !parameter.interface)
        continue;
      SyntaxType term;
      term.name = parameter.name;
      term.span = expr.span;
      auto component = checker.type(decl, term);
      if (!component)
        return {};
      auto &interface = checker.output.declarations[parameter.interface->index];
      for (auto id : interface.members)
        if (checker.output.declarations[id.index].name == parts.second)
          return ExpressionTypes::Callable{id, *component};
      fail("source.call", "unknown interface member", expr.span);
      return {};
    }
  // A bound component member takes precedence over a nominal alternative.
  auto alternative = StringRef(expr.text).rsplit("::");
  if (!alternative.second.empty()) {
    auto nominal = checker.resolve(decl, alternative.first, expr.span, false);
    if (nominal && checker.output.declarations[nominal->index].kind ==
                       Declaration::Kind::Variant)
      return ExpressionTypes::Callable{*nominal, {}};
  }
  auto id = checker.resolve(decl, expr.text, expr.span);
  if (!id)
    return {};
  if (checker.output.declarations[id->index].abstract &&
      checker.output.declarations[id->index].kind !=
          Declaration::Kind::Associated) {
    fail("source.call", "abstract call requires a bound component", expr.span);
    return {};
  }
  return ExpressionTypes::Callable{*id, {}};
}
} // namespace zkc::language::detail
