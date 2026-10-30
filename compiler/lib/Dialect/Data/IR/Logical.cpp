#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Data/Layout.h"
#include "zkc/Dialect/Diagnostics.h"
#include <set>
using namespace mlir;
namespace zkc::data {
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
