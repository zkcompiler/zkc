#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"

using namespace llvm;
using namespace mlir;
#include "zkc/Interfaces/LinearContraction.cpp.inc"

namespace zkc {
namespace {
const protocol::OperationContracts *semanticRoles(Operation *op) {
  auto apply = dyn_cast<exec::ApplyOp>(op);
  if (!apply)
    return {};
  auto binding = protocol::operationBinding(op);
  if (!binding) {
    consumeError(binding.takeError());
    return {};
  }
  auto rawParameters = apply.getParametersAttr();
  if (!rawParameters)
    return {};
  SmallVector<std::string> parameters;
  for (Attribute parameter : rawParameters) {
    auto value = dyn_cast<StringAttr>(parameter);
    if (!value)
      return {};
    parameters.push_back(value.str());
  }
  if (auto error =
          protocol::checkParameters(binding->application, parameters)) {
    consumeError(std::move(error));
    return {};
  }
  // An explicit physical choice does not change the logical roles.
  binding->application.implementation.clear();
  auto logical = protocol::resolveBinding(binding->application, false);
  if (!logical) {
    consumeError(logical.takeError());
    return {};
  }
  auto typesMatch = [&](TypeRange actual,
                        ArrayRef<protocol::BoundType> expected) {
    if (actual.size() != expected.size())
      return false;
    for (auto [type, target] : zip(actual, expected))
      if (type != protocol::decodeBoundType(op->getContext(), target))
        return false;
    return true;
  };
  if (!typesMatch(apply.getInputs().getTypes(), logical->inputs) ||
      !typesMatch(apply.getOutcome().getType().getPayload(), logical->outputs))
    return {};
  return protocol::operationContracts(binding->application.contract);
}
std::optional<DiagonalProducerRoles> producerRoles(Operation *op) {
  const auto *facts = semanticRoles(op);
  if (!facts || !facts->diagonalMap)
    return {};
  const auto &map = *facts->diagonalMap;
  return DiagonalProducerRoles{map.factorsOperand, map.valuesOperand,
                               map.result};
}
std::optional<DiagonalContractionRoles> consumerRoles(Operation *op) {
  const auto *facts = semanticRoles(op);
  if (!facts || !facts->linearContraction)
    return {};
  const auto &contraction = *facts->linearContraction;
  return DiagonalContractionRoles{contraction.coefficientsOperand,
                                  contraction.valuesOperand};
}
} // namespace
std::optional<DiagonalProducerRoles>
zkc::exec::ApplyOp::getDiagonalProducerRoles() {
  return producerRoles(*this);
}
std::optional<DiagonalContractionRoles>
zkc::exec::ApplyOp::getDiagonalContractionRoles() {
  return consumerRoles(*this);
}
} // namespace zkc
