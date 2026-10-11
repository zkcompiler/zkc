#ifndef ZKC_ANALYSIS_FINITE_CARDINALITY_INTERNAL_H
#define ZKC_ANALYSIS_FINITE_CARDINALITY_INTERNAL_H
#include "zkc/Contracts/FiniteCardinality.h"
#include "zkc/Dialect/Data/IR/DataOps.h"

namespace zkc::finite::detail {
inline facts::DomainRef domainRef(mlir::Value value) {
  return reinterpret_cast<uintptr_t>(value.getAsOpaquePointer());
}
inline mlir::Value domainValue(facts::DomainRef ref) {
  return mlir::Value::getFromOpaquePointer(reinterpret_cast<void *>(ref));
}
/// Constructor structure only. The caller independently substitutes leaves
/// and derives their evidence under its own subject and shared allowance.
inline facts::DomainNode cardinalityNode(facts::DomainRef ref) {
  auto *op = domainValue(ref).getDefiningOp();
  facts::DomainNode node;
  if (!op)
    return node;
  if (mlir::isa<data::DomainZipOp, data::DomainProductOp>(op)) {
    node.kind = mlir::isa<data::DomainZipOp>(op) ? facts::DomainKind::Zip
                                                 : facts::DomainKind::Product;
    node.children = op->getNumOperands();
  } else if (mlir::isa<data::DomainMatrixCoordinatesOp>(op)) {
    node.kind = facts::DomainKind::MatrixCoordinates;
    node.extent.value = domainRef(op->getOperand(0));
  } else if (auto range = mlir::dyn_cast<data::DomainRangeOp>(op)) {
    node.kind = facts::DomainKind::Range;
    node.lower = domainRef(range.getLower());
    node.upper = domainRef(range.getUpper());
  } else if (mlir::isa<data::DomainElementsOp, data::DomainIndicesOp,
                       data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(
                 op)) {
    node.kind = facts::DomainKind::Extent;
    node.extent = {domainRef(op->getOperand(0)),
                   mlir::isa<data::DomainMatrixRowOp>(op) ? 1u : 0u};
    if (auto indices = mlir::dyn_cast<data::DomainIndicesOp>(op))
      node.extent.axis = indices.getAxis();
  }
  return node;
}
inline facts::DomainRef cardinalityChild(facts::DomainRef ref, size_t index) {
  return domainRef(domainValue(ref).getDefiningOp()->getOperand(index));
}
} // namespace zkc::finite::detail
#endif
