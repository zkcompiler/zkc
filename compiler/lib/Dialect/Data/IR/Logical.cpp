#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Data/Layout.h"
#include "zkc/Dialect/Diagnostics.h"
#include <set>
using namespace mlir;
namespace zkc::data {
namespace {
LogicalResult refuse(Operation *op, StringRef reason) {
  return diagnostics::emit(op->emitOpError(), "data-value-formation", reason);
}
bool productLayout(LayoutAttr layout) {
  auto kind = layout.getKind().getValue();
  return kind == "unit" || kind == "tuple" || kind == "array" ||
         kind == "record" || kind == "associated";
}
bool payloadTypes(ArrayRef<LayoutFieldAttr> fields, TypeRange types) {
  if (fields.size() != types.size())
    return false;
  for (auto [field, type] : llvm::zip(fields, types))
    if (valueType(field.getLayout()) != type)
      return false;
  return true;
}
} // namespace
LogicalResult ConstructOp::verify() {
  auto layout = getOutput().getType().getLayout();
  auto fields = layout.getFields();
  if (layout.getKind().getValue() == "variant") {
    auto arms = layout.getAlternatives();
    auto found = llvm::find_if(arms, [&](LayoutAlternativeAttr arm) {
      return arm.getName().getValue() == getAlternative();
    });
    if (found == arms.end())
      return refuse(*this, "unknown logical alternative");
    fields = found->getFields();
  } else if (!productLayout(layout) || !getAlternative().empty())
    return refuse(*this, "product construction has no alternative");
  if (!payloadTypes(fields, getInputs().getTypes()))
    return refuse(*this, "constructor payload differs from layout");
  return success();
}
LogicalResult UnpackOp::verify() {
  auto layout = getInput().getType().getLayout();
  if (!productLayout(layout) ||
      !payloadTypes(layout.getFields(), getOutputs().getTypes()))
    return refuse(*this, "product elimination differs from layout");
  return success();
}
LogicalResult ProjectOp::verify() {
  if (getPath().size() > 64)
    return refuse(*this, "projection path exceeds structural depth");
  Type selected = getInput().getType();
  for (auto index : getPath()) {
    auto value = dyn_cast<ValueType>(selected);
    if (!value || !value.getLayout().getAlternatives().empty() || index < 0 ||
        uint64_t(index) >= value.getLayout().getFields().size())
      return refuse(*this, "projection selects no logical field");
    selected = valueType(value.getLayout().getFields()[index].getLayout());
  }
  if (selected != getOutput().getType())
    return refuse(*this, "projection result differs from selected field");
  return success();
}
LogicalResult MatchOp::verify() {
  auto fail = [&] {
    return diagnostics::emit(emitOpError(), "data-match-formation",
                             "sum alternatives or payload types differ");
  };
  auto layout = getInput().getType().getLayout();
  auto alternatives = layout.getAlternatives();
  if (layout.getKind().getValue() != "variant" ||
      alternatives.size() != getArms().size() ||
      getAlternatives().size() != getArms().size())
    return fail();
  std::set<StringRef> names;
  for (auto [name, block] : llvm::zip(getAlternatives(), getArms())) {
    auto label = cast<StringAttr>(name).getValue();
    if (!names.insert(label).second)
      return fail();
    auto found = llvm::find_if(alternatives, [&](LayoutAlternativeAttr arm) {
      return arm.getName().getValue() == label;
    });
    if (found == alternatives.end())
      return fail();
    auto fields = found->getFields();
    if (block->getNumArguments() != fields.size() + getCaptures().size())
      return fail();
    for (auto [field, argument] :
         llvm::zip(fields, block->getArguments().take_front(fields.size())))
      if (argument.getType() != valueType(field.getLayout()))
        return fail();
    if (TypeRange(block->getArguments().drop_front(fields.size())) !=
        getCaptures().getTypes())
      return fail();
  }
  return success();
}
SuccessorOperands MatchOp::getSuccessorOperands(unsigned index) {
  auto count = getArms()[index]->getNumArguments();
  return SuccessorOperands(
      count >= getCaptures().size() ? count - getCaptures().size() : 0,
      getCapturesMutable());
}
} // namespace zkc::data
