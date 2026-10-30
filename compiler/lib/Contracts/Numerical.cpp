#include "zkc/Contracts/Numerical.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"

using namespace llvm;
namespace zkc::protocol {
namespace {
const generic::Operation *numericalDeclaration(StringRef contract) {
  for (const auto &operation : executableOperationContracts())
    if (operation.name == contract && operation.numerical)
      return &operation;
  return nullptr;
}
} // namespace
bool numericalContract(StringRef contract) {
  return numericalDeclaration(contract) != nullptr;
}
Error checkNumericalArguments(const BindingApplication &binding) {
  if (!numericalContract(binding.contract))
    return error("binding-contract");
  if (binding.arguments.size() != 2)
    return error("binding-static-arity");
  if (installedIdentitySort(binding.arguments[0]) != "Field")
    return error("binding-static-identity");
  StringRef mask = binding.arguments[1];
  if (mask.size() > NumericalLimits::slots ||
      !all_of(mask, [](char c) { return c == '0' || c == '1'; }))
    return error("numerical-mask");
  return Error::success();
}
Expected<BoundOperation>
resolveNumericalSignature(const BindingApplication &binding) {
  if (auto e = checkNumericalArguments(binding))
    return e;
  const auto &field = binding.arguments[0];
  const auto &family = *numericalDeclaration(binding.contract)->numerical;
  BoundOperation result{{BoundType{"index", "", ""}}, {}};
  for (char bit : binding.arguments[1])
    result.inputs.push_back({bit == '1' ? "vector" : "field", field, ""});
  result.outputs.push_back(
      {family.result == generic::NumericalSignature::Result::Map ? "vector"
                                                                 : "field",
       field, ""});
  return result;
}
Expected<ring::Expression>
readNumericalExpression(StringRef body, StringRef field, size_t slots) {
  if (body.size() > NumericalLimits::bodyBytes)
    return error("numerical-body-limit");
  if (slots > NumericalLimits::slots)
    return error("numerical-mask");
  auto expression = ring::readExpressionText(body);
  if (!expression)
    return expression.takeError();
  if (zkc::printJson(expression->encode()) != body)
    return error("numerical-body-canonical");
  if (installedIdentitySort(field) != "Field" ||
      expression->inputs().size() != slots || expression->outputs().size() != 1)
    return error("numerical-body-signature");
  for (const auto &input : expression->inputs())
    if (input.field != field)
      return error("numerical-body-field");
  for (auto [node, fact] : zip(expression->nodes(), expression->facts()))
    if (node.kind == ring::Kind::Embed || fact.field != field)
      return error("numerical-body-field");
  return std::move(*expression);
}
Error checkNumericalParameters(const BindingApplication &binding,
                               ArrayRef<std::string> parameters) {
  if (auto e = checkNumericalArguments(binding))
    return e;
  if (parameters.size() != 1)
    return error("interactive-kernel-parameters");
  auto expression = readNumericalExpression(
      parameters.front(), binding.arguments[0], binding.arguments[1].size());
  return expression ? Error::success() : expression.takeError();
}
} // namespace zkc::protocol
