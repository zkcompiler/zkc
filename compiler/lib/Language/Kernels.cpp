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
                             std::vector<Type> &arguments,
                             std::vector<std::string> &parameters) {
  for (const auto &syntax : expr.arguments) {
    auto type = checker.type(decl, syntax);
    if (!type)
      return {};
    arguments.push_back(std::move(*type));
  }
  parameters = expr.labels;
  for (const auto &parameter : expr.assetParameters) {
    auto position = parameter.first;
    const auto &name = parameter.second;
    if (!checker.types.charge(checker.output.assets.size() + name.size() + 1,
                              expr.span))
      return {};
    auto found = llvm::find_if(checker.output.assets, [&](const auto &asset) {
      return asset.name() == name;
    });
    if (found == checker.output.assets.end()) {
      fail("source.asset-reference", "captured asset is absent", expr.span);
      return {};
    }
    if (!StringRef(expr.text).starts_with("ring.") || position != 0 ||
        !found->ring()) {
      fail("source.asset-reference",
           "operation does not accept this asset kind", expr.span);
      return {};
    }
    parameters[position] = found->identity().str();
  }
  return checker.types.kernelSignature(expr.text, arguments, parameters,
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
  std::vector<std::string> parameters;
  auto signature = kernelSignature(expr, arguments, parameters);
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
  LocalPrimitive primitive{expr.text, std::move(operands),
                           std::move(parameters)};
  primitive.bindingArguments = std::move(arguments);
  // The installed local envelope does not certify totality.
  body.mayStop = true;
  return emit(std::move(primitive), result, {}, expr.span);
}
} // namespace zkc::language::detail
