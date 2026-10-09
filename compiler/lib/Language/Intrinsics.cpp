#include "BodyCheck.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Language/Builtins.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
std::optional<Semantics::CallSignature>
BodyChecker::intrinsicSignature(const Expression &expr,
                                std::vector<Type> &arguments) {
  for (const auto &syntax : expr.arguments) {
    auto type = checker.type(decl, syntax);
    if (!type)
      return {};
    arguments.push_back(std::move(*type));
  }
  return checker.types.intrinsicSignature(&decl, expr.text, arguments,
                                          expr.labels, expr.span);
}

std::optional<ValueId> BodyChecker::intrinsic(const Expression &expr,
                                              unsigned depth) {
  if (!math()) {
    fail("source.mode", "mathematical intrinsics require a math function",
         expr.span);
    return {};
  }
  std::vector<Type> arguments;
  auto signature = intrinsicSignature(expr, arguments);
  if (!signature)
    return {};
  if (expr.children.size() != signature->inputs.size()) {
    fail("source.intrinsic", "intrinsic input count differs", expr.span);
    return {};
  }
  std::vector<ValueId> operands;
  for (unsigned i = 0; i < expr.children.size(); ++i) {
    auto value = expression(expr.children[i], signature->inputs[i], depth + 1);
    if (!value || !use(*value, expr.span))
      return {};
    operands.push_back(*value);
  }
  auto components = combine(operands, expr.span);
  if (!components)
    return {};
  if (!components->empty())
    body.formationRequirements.push_back(*components);
  return emit(MathValue{mathematicalIntrinsic(expr.text)->identity,
                        std::move(operands),
                        {},
                        std::move(arguments),
                        expr.labels},
              signature->resultType(), std::move(*components), expr.span);
}
} // namespace zkc::language::detail
