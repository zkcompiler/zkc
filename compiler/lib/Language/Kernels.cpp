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
                             std::vector<std::string> &parameters,
                             std::vector<AssetReference> &references) {
  for (const auto &syntax : expr.arguments) {
    auto type = checker.type(decl, syntax);
    if (!type)
      return {};
    arguments.push_back(std::move(*type));
  }
  parameters = expr.labels;
  // The installed parameter contract decides which position takes an asset
  // term; an asset-identity parameter is never spelled as a literal digest.
  const auto *schema = protocol::parameterContract(expr.text);
  bool assetPosition =
      schema &&
      schema->validator == protocol::ParameterValidator::AssetIdentity;
  StringRef expectedAssetSort;
  if (assetPosition) {
    if (schema->assetFormat == "zkc.ring/0")
      expectedAssetSort = "Ring";
    else if (schema->assetFormat == "zkc.relation-bundle/0")
      expectedAssetSort = "Bundle";
  }
  if (assetPosition && !expr.assetParameters.count(0)) {
    fail("source.asset-reference",
         "operation parameter requires a captured asset term", expr.span);
    return {};
  }
  bool closedParameters = true;
  for (const auto &[position, syntax] : expr.assetParameters) {
    auto term = checker.type(decl, syntax);
    if (!term)
      return {};
    if (term->kind != Type::Kind::Asset) {
      fail("source.asset-reference",
           "kernel parameter term is not a captured asset", expr.span);
      return {};
    }
    if (!assetPosition || position != 0 ||
        assetSort(*term) != expectedAssetSort) {
      fail("source.asset-reference",
           "operation does not accept this asset term", expr.span);
      return {};
    }
    if (term->symbolic) {
      closedParameters = false;
      parameters[position].clear();
    } else
      parameters[position] = term->domain;
    references.push_back({position, std::move(*term)});
  }
  return checker.types.kernelSignature(expr.text, arguments, parameters,
                                       expr.span, &decl, closedParameters);
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
  std::vector<AssetReference> references;
  auto signature = kernelSignature(expr, arguments, parameters, references);
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
  primitive.assetReferences = std::move(references);
  // The installed local envelope does not certify totality.
  body.mayStop = true;
  return emit(std::move(primitive), result, {}, expr.span);
}
} // namespace zkc::language::detail
