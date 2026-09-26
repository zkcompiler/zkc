#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"

using namespace llvm;
using namespace mlir;
#include "zkc/Interfaces/LinearContraction.cpp.inc"

namespace zkc {
namespace {
const protocol::OperationContracts *semanticRoles(Operation *op) {
  auto binding = protocol::operationBinding(op);
  if (!binding) {
    consumeError(binding.takeError());
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
  if (op->getName().getStringRef() !=
          protocol::boundOperationName(binding->application.contract) ||
      !typesMatch(op->getOperandTypes(), logical->inputs) ||
      !typesMatch(op->getResultTypes(), logical->outputs))
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
std::optional<DiagonalProducerRoles> VectorMulOp::getDiagonalProducerRoles() {
  return producerRoles(*this);
}
std::optional<DiagonalProducerRoles>
CurveScaleEachOp::getDiagonalProducerRoles() {
  return producerRoles(*this);
}
std::optional<DiagonalContractionRoles>
VectorDotOp::getDiagonalContractionRoles() {
  return consumerRoles(*this);
}
std::optional<DiagonalContractionRoles>
CurveMSMOp::getDiagonalContractionRoles() {
  return consumerRoles(*this);
}
} // namespace zkc
