#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"

using namespace llvm;
using namespace mlir;
#include "zkc/Interfaces/LinearContraction.cpp.inc"

namespace zkc {
namespace {
struct Selection {
  const protocol::OperationContracts *facts;
  std::string representation, implementation;
};
std::optional<Selection> selection(Operation *op, bool producer) {
  auto binding = protocol::operationBinding(op);
  if (!binding) {
    consumeError(binding.takeError());
    return {};
  }
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
  const auto *facts =
      protocol::operationContracts(binding->application.contract);
  if (!facts || (producer ? !facts->diagonalMap : !facts->linearContraction))
    return {};
  const auto &port =
      producer ? logical->outputs[facts->diagonalMap->result]
               : logical->inputs[facts->linearContraction->valuesOperand];
  auto *representation = protocol::installedDomains().representationForLayout(
      port.kind, port.identity, "diagonal");
  if (!representation)
    return {};
  auto family = StringRef(representation->identity).split('.').first;
  binding->application.implementation =
      (family + "-diagonal/" + binding->application.contract).str();
  auto physical = protocol::resolveBinding(binding->application, true);
  if (!physical) {
    consumeError(physical.takeError());
    return {};
  }
  return Selection{facts, representation->identity,
                   binding->application.implementation};
}
std::optional<DiagonalProducerSelection> producerSelection(Operation *op) {
  auto selected = selection(op, true);
  if (!selected)
    return {};
  const auto &map = *selected->facts->diagonalMap;
  return DiagonalProducerSelection{map.factorsOperand, map.valuesOperand,
                                   map.result, selected->representation,
                                   selected->implementation};
}
std::optional<DiagonalContractionSelection> consumerSelection(Operation *op) {
  auto selected = selection(op, false);
  if (!selected)
    return {};
  const auto &contraction = *selected->facts->linearContraction;
  return DiagonalContractionSelection{
      contraction.coefficientsOperand, contraction.valuesOperand,
      selected->representation, selected->implementation};
}
} // namespace
std::optional<DiagonalProducerSelection>
VectorMulOp::getDiagonalProducerSelection() {
  return producerSelection(*this);
}
std::optional<DiagonalProducerSelection>
CurveScaleEachOp::getDiagonalProducerSelection() {
  return producerSelection(*this);
}
std::optional<DiagonalContractionSelection>
VectorDotOp::getDiagonalContractionSelection() {
  return consumerSelection(*this);
}
std::optional<DiagonalContractionSelection>
CurveMSMOp::getDiagonalContractionSelection() {
  return consumerSelection(*this);
}
} // namespace zkc
