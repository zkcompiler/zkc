#include "DataPreconditions.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Support/Refusal.h"
using namespace llvm;
namespace zkc::language {
Expected<std::vector<NativeDataPrecondition>>
flattenDataPreconditions(const Declaration &decl, Layouts &layouts) {
  if (decl.dataPreconditions.size() > 1024)
    return error("source.limit", "helper exceeds 1024 data preconditions");
  std::vector<NativeDataPrecondition> result;
  for (const auto &condition : decl.dataPreconditions) {
    auto left = layouts.selectInput(decl, condition.left);
    if (!left)
      return left.takeError();
    auto right = layouts.selectInput(decl, condition.right);
    if (!right)
      return right.takeError();
    if (left->layout->leaves.size() != 1 || right->layout->leaves.size() != 1 ||
        left->layout->custody || right->layout->custody)
      return error("source.data-bound",
                   "precondition requires individual native data ports");
    result.push_back({condition.kind, left->offset, right->offset,
                      condition.leftAxis, condition.rightAxis});
  }
  return result;
}
mlir::ArrayAttr
emitDataPreconditions(mlir::MLIRContext *context,
                      ArrayRef<NativeDataPrecondition> conditions) {
  SmallVector<mlir::Attribute> result;
  for (const auto &condition : conditions)
    if (condition.kind == DataPrecondition::Kind::IndexBound)
      result.push_back(data::IndexBoundAttr::get(
          context, condition.left, condition.right, condition.rightAxis));
    else
      result.push_back(data::EqualExtentAttr::get(
          context, condition.left, condition.leftAxis, condition.right,
          condition.rightAxis));
  return mlir::ArrayAttr::get(context, result);
}
bool compareDataPreconditions(mlir::Operation &op,
                              ArrayRef<NativeDataPrecondition> conditions) {
  auto attributes = op.getAttrOfType<mlir::ArrayAttr>("data.preconditions");
  if (conditions.empty())
    return !op.hasAttr("data.preconditions");
  if (!attributes || attributes.size() != conditions.size())
    return false;
  for (unsigned i = 0; i < conditions.size(); ++i) {
    const auto &condition = conditions[i];
    if (condition.kind == DataPrecondition::Kind::IndexBound) {
      auto bound = mlir::dyn_cast<data::IndexBoundAttr>(attributes[i]);
      if (!bound || bound.getIndexArg() != condition.left ||
          bound.getContainerArg() != condition.right ||
          bound.getAxis() != condition.rightAxis)
        return false;
    } else {
      auto equal = mlir::dyn_cast<data::EqualExtentAttr>(attributes[i]);
      if (!equal || equal.getLeftArg() != condition.left ||
          equal.getLeftAxis() != condition.leftAxis ||
          equal.getRightArg() != condition.right ||
          equal.getRightAxis() != condition.rightAxis)
        return false;
    }
  }
  return true;
}
} // namespace zkc::language
