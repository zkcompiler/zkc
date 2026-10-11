#include "zkc/Analysis/Finite.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "llvm/ADT/DenseSet.h"
using namespace mlir;
namespace zkc::data {
namespace {
LogicalResult refuse(Operation *op, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), "finite-domain", detail);
}
LogicalResult constructor(Operation *op, ArrayRef<Type> items,
                          ArrayRef<StringRef> attributes = {}) {
  if (!isa_and_nonnull<DomainOp>(op->getParentOp()))
    return refuse(op, "constructor must belong directly to a data.domain");
  for (auto attr : op->getAttrs())
    if (!llvm::is_contained(attributes, attr.getName().getValue()))
      return refuse(op, "unexpected constructor attribute");
  auto output = dyn_cast<DomainType>(op->getResult(0).getType());
  if (!output || output.getItemTypes() != items)
    return refuse(op, "domain item signature");
  return success();
}
LogicalResult composite(Operation *op) {
  if (!op->getNumOperands())
    return refuse(op, "zip/product requires at least one factor");
  SmallVector<Type> types;
  for (auto input : op->getOperandTypes()) {
    auto domain = dyn_cast<DomainType>(input);
    if (!domain)
      return refuse(op, "expected domain factors");
    llvm::append_range(types, domain.getItemTypes());
  }
  return constructor(op, types);
}
Type indexType(MLIRContext *ctx) {
  return IntegerType::get(ctx, 64, IntegerType::Unsigned);
}
LogicalResult matrixView(Operation *op) {
  auto element = finite::elementType(op->getOperand(0).getType(), true);
  if (!element)
    return refuse(op, "expected a canonical matrix");
  return constructor(op, {element});
}
} // namespace
LogicalResult DomainType::verify(function_ref<InFlightDiagnostic()> emit,
                                 ArrayRef<Type> items) {
  if (items.empty() || items.size() > 1024)
    return emit() << "expected between one and 1024 domain items";
  for (auto type : items) {
    auto bound = protocol::encodeBoundType(type, false);
    if (!bound) {
      llvm::consumeError(bound.takeError());
      return emit() << "domain items must be canonical native data";
    }
    if (!protocol::duplicable(*bound) || !protocol::discardable(*bound))
      return emit() << "domain items must permit Copy and Drop";
  }
  return success();
}
LogicalResult DomainOp::verifyRegions() {
  auto signature = getFunctionType();
  if (getSymVisibility() != "private" || getBody().empty() ||
      signature.getNumResults() != 1 ||
      !isa<DomainType>(signature.getResult(0)) ||
      getBody().front().getArgumentTypes() != signature.getInputs() ||
      (*this)->getAttrs().size() != 3)
    return refuse(*this, "expected private isolated typed domain declaration");
  for (auto type : signature.getInputs()) {
    auto bound = protocol::encodeBoundType(type, false);
    if (!bound) {
      llvm::consumeError(bound.takeError());
      return refuse(*this, "domain arguments must have native encoding");
    }
    if (!protocol::duplicable(*bound) || !protocol::discardable(*bound))
      return refuse(*this, "domain arguments must be native Copy/Drop values");
  }
  if (signature.getNumInputs() > 1024 ||
      getBody().front().getOperations().size() > 4096)
    return refuse(*this, "domain declaration exceeds bounded formation work");
  auto &block = getBody().front();
  auto yield =
      block.empty() ? DomainYieldOp() : dyn_cast<DomainYieldOp>(block.back());
  if (!yield || yield.getInput().getType() != signature.getResult(0))
    return refuse(*this, "domain return signature");
  llvm::DenseSet<Value> available(block.getArguments().begin(),
                                  block.getArguments().end());
  llvm::DenseMap<Value, unsigned> depths;
  for (auto &op : block) {
    if (!isa<DomainElementsOp, DomainIndicesOp, DomainRangeOp, DomainZipOp,
             DomainProductOp, DomainMatrixRowOp, DomainMatrixColumnOp,
             DomainMatrixCoordinatesOp, DomainYieldOp>(op))
      return refuse(&op, "descriptor admits only typed domain constructors");
    for (Value operand : op.getOperands())
      if (!available.contains(operand))
        return refuse(&op, "domain operand must precede its use");
    unsigned depth = 1;
    for (Value operand : op.getOperands())
      depth = std::max(depth, depths.lookup(operand) + 1);
    if (depth > 64)
      return refuse(&op, "domain constructor depth exceeds 64");
    for (Value value : op.getResults())
      depths[value] = depth;
    available.insert(op.getResults().begin(), op.getResults().end());
  }
  return success();
}
LogicalResult DomainElementsOp::verify() {
  auto element = finite::elementType(getInput().getType());
  if (!element)
    return refuse(*this,
                  "elements requires a one-dimensional native collection");
  return constructor(*this, {element});
}
LogicalResult DomainIndicesOp::verify() {
  auto type = getInput().getType();
  auto axis = getAxisAttr().getInt();
  auto tensor = dyn_cast<RankedTensorType>(type);
  if (axis < 0 || (tensor ? axis >= tensor.getRank() : axis != 0) ||
      (!finite::elementType(type) && !finite::elementType(type, true)))
    return refuse(*this, "indices requires a valid explicit collection axis");
  return constructor(*this, {indexType(getContext())}, {"axis"});
}
LogicalResult DomainRangeOp::verify() {
  return constructor(*this, {indexType(getContext())});
}
LogicalResult DomainZipOp::verify() { return composite(*this); }
LogicalResult DomainProductOp::verify() { return composite(*this); }
LogicalResult DomainMatrixRowOp::verify() { return matrixView(*this); }
LogicalResult DomainMatrixColumnOp::verify() { return matrixView(*this); }
LogicalResult DomainMatrixCoordinatesOp::verify() {
  if (!finite::elementType(getInput().getType(), true) ||
      (getOrder() != "row_major" && getOrder() != "column_major"))
    return refuse(*this,
                  "matrix coordinates require an explicit traversal order");
  auto index = indexType(getContext());
  return constructor(*this, {index, index}, {"order"});
}
LogicalResult BoundedAtOp::verify() {
  if (!(*this)->getAttrs().empty() ||
      finite::elementType(getInput().getType()) != getOutput().getType() ||
      !finite::provesBound(getIndex(), getInput(), 0))
    return diagnostics::emit(
        emitOpError(), "finite-bound",
        "lookup requires exact container/index provenance");
  return success();
}
LogicalResult BoundedMatrixAtOp::verify() {
  if (!(*this)->getAttrs().empty() ||
      finite::elementType(getInput().getType(), true) !=
          getOutput().getType() ||
      !finite::provesBound(getRow(), getInput(), 0) ||
      !finite::provesBound(getColumn(), getInput(), 1))
    return diagnostics::emit(
        emitOpError(), "finite-bound",
        "matrix lookup requires both exact coordinate bounds");
  return success();
}
} // namespace zkc::data
