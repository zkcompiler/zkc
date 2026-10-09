#include "zkc/Contracts/Domains.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/Diagnostics.h"

using namespace mlir;

namespace zkc::algebra {
Type mapField(FunctionType type, ArrayRef<bool> rowwise) {
  if (!type || type.getNumInputs() != rowwise.size() ||
      type.getNumResults() != 1 || !llvm::is_contained(rowwise, true))
    return {};
  auto vector = dyn_cast<RankedTensorType>(type.getResult(0));
  if (!vector || vector.getRank() != 1 || !vector.isDynamicDim(0) ||
      vector.getEncoding())
    return {};
  auto field = dyn_cast<FieldType>(vector.getElementType());
  if (!field ||
      protocol::installedDomains().identitySort(field.getDomain()) != "Field")
    return {};
  for (auto [input, mapped] : llvm::zip(type.getInputs(), rowwise))
    if (input != (mapped ? Type(vector) : Type(field)))
      return {};
  return field;
}

LogicalResult MapRealizeOp::verify() {
  if ((*this)->getAttrs().size() != 4 ||
      !mapField(getFunctionType(), getRowwise()))
    return diagnostics::emit(
        emitOpError(), "algebra-map-signature",
        "expected one scalar field, a vector result and at least one rowwise "
        "vector input");
  return success();
}

LogicalResult MapRealizeOp::verifySymbolUses(SymbolTableCollection &tables) {
  // Only an existing private sibling helper is mapped. Its body and every
  // nested helper are checked by the Ring view when the map is realized.
  auto helper =
      tables.lookupNearestSymbolFrom<func::FuncOp>(*this, getHelperAttr());
  if (!helper || failed(helper->getName().verifyInvariants(helper)) ||
      helper.isExternal() || !helper.isPrivate() ||
      helper->getParentOp() != (*this)->getParentOp())
    return diagnostics::emit(emitOpError(), "algebra-map-helper",
                             "expected a private sibling helper body");
  auto field = mapField(getFunctionType(), getRowwise());
  auto attribute = helper->getAttrOfType<TypeAttr>("function_type");
  SmallVector<Type> scalars(getRowwise().size(), field);
  if (!field || !attribute ||
      attribute.getValue() != FunctionType::get(getContext(), scalars, {field}))
    return diagnostics::emit(emitOpError(), "algebra-map-signature",
                             "helper ports must be the mapped scalar field");
  return success();
}
} // namespace zkc::algebra
