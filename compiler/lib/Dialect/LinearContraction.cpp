#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Dialect/Algebra/Parameters.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/InvocationParameters.h"

using namespace llvm;
using namespace mlir;
#include "zkc/Interfaces/LinearContraction.cpp.inc"

namespace zkc {
namespace {
const protocol::OperationContracts *semanticRoles(Operation *op) {
  auto apply = dyn_cast<exec::ApplyOp>(op);
  if (!apply)
    return {};
  auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
      op, apply.getBindingAttr());
  if (!binding || !apply.getParametersAttr())
    return {};
  auto silent = [&] {
    auto diagnostic = emitError(op->getLoc());
    diagnostic.abandon();
    return diagnostic;
  };
  if (failed(verifyInvocationParameters(silent, binding.getContract(),
                                        binding.getArgumentsAttr(),
                                        apply.getParametersAttr())))
    return {};
  // A selected implementation does not change the logical roles. Resident
  // ports only match when they retain this exact mathematical signature.
  auto logical =
      resolveLogicalSignature(silent, op->getContext(), binding.getContract(),
                              binding.getArguments().getValue());
  if (!logical || !equal(apply.getInputs().getTypes(), logical.getInputs()) ||
      !equal(apply.getOutcome().getType().getPayload(), logical.getResults()))
    return {};
  return protocol::operationContracts(binding.getContract());
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
