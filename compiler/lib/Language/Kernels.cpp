#include "zkc/Contracts/Kernels.h"
#include "BodyCheck.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Language/Builtins.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
std::optional<Semantics::CallSignature>
BodyChecker::kernelSignature(const Expression &expr,
                             std::vector<Type> &arguments) {
  for (const auto &syntax : expr.arguments) {
    auto type = checker.type(decl, syntax);
    if (!type)
      return {};
    arguments.push_back(std::move(*type));
  }
  return checker.types.kernelSignature(expr.text, arguments, expr.labels,
                                       expr.span, &decl);
}

std::optional<ValueId> BodyChecker::kernel(const Expression &expr,
                                           unsigned depth) {
  if (!local()) {
    fail("source.mode", "kernel bindings require an ordinary local function",
         expr.span);
    return {};
  }
  std::vector<Type> arguments;
  auto signature = kernelSignature(expr, arguments);
  if (!signature)
    return {};
  if (expr.children.size() != signature->inputs.size()) {
    fail("source.kernel", "installed input count differs", expr.span);
    return {};
  }
  std::vector<ValueId> operands;
  for (unsigned i = 0; i < expr.children.size(); ++i) {
    auto input = expression(expr.children[i], signature->inputs[i], depth + 1);
    if (!input || !use(*input, expr.span))
      return {};
    operands.push_back(*input);
  }
  Type result = signature->resultType();
  LocalPrimitive primitive{expr.text, std::move(operands), expr.labels};
  primitive.bindingArguments = std::move(arguments);
  // The installed local envelope does not certify totality.
  body.mayStop = true;
  return emit(std::move(primitive), result, {}, expr.span);
}
} // namespace zkc::language::detail
