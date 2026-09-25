#include "zkc/Dialect/IR.h"
#include "zkc/Protocol/Bindings.h"
#include "zkc/Protocol/Contracts.h"
#include "zkc/Protocol/Domains.h"

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
  auto logical = protocol::resolveBinding(*binding, false);
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
  if (op->getName().getStringRef() != logical->operation ||
      !typesMatch(op->getOperandTypes(), logical->inputs) ||
      !typesMatch(op->getResultTypes(), logical->outputs))
    return {};
  const auto *facts = protocol::operationContracts(binding->contract);
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
  binding->implementation = (family + "-diagonal/" + binding->contract).str();
  auto physical = protocol::resolveBinding(*binding, true);
  if (!physical) {
    consumeError(physical.takeError());
    return {};
  }
  return Selection{facts, representation->identity, binding->implementation};
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
