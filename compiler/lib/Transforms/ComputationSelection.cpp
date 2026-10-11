#include "ComputationSelection.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
ComputationSelection selectComputation(finite::Computation computation,
                                       MathematicalSelectionPolicy policy) {
  ComputationSelection selection;
  if (!policy.finiteBulk)
    return selection;
  selection.view = finite::analyzeComputation(computation);
  if (!selection.view)
    return selection;
  selection.bilinear = finite::recognizeBilinear(computation);
  if (selection.bilinear)
    selection.kind = RealizationKind::Bilinear;
  else if (selection.view->reduction)
    selection.kind = RealizationKind::Reduction;
  else if (selection.view->elementwise)
    selection.kind = RealizationKind::Elementwise;
  return selection;
}
std::optional<finite::Elementwise> selectLaneFormula(Block &formula,
                                                     ArrayRef<bool> rowwise) {
  if (formula.empty() || formula.getNumArguments() != rowwise.size() ||
      formula.back().getNumOperands() != 1)
    return std::nullopt;
  Type field = formula.back().getOperand(0).getType();
  if (!isa<algebra::FieldType>(field))
    return std::nullopt;
  llvm::DenseMap<Value, finite::FormulaMode> modes;
  for (auto [i, argument] : enumerate(formula.getArguments()))
    modes[argument] =
        rowwise[i] ? finite::FormulaMode::Rows : finite::FormulaMode::Scalar;
  return finite::recognizeFormula(formula, field, std::move(modes));
}
std::optional<std::pair<unsigned, unsigned>>
selectMapProduct(Block &formula, ArrayRef<bool> rowwise) {
  if (!selectLaneFormula(formula, rowwise))
    return std::nullopt;
  auto *product = formula.back().getOperand(0).getDefiningOp();
  auto *contract = product ? finite::semantics(product) : nullptr;
  if (!contract || contract->identity != MathematicalIdentity::FieldMultiply ||
      product->getNumOperands() != 2)
    return std::nullopt;
  auto left = dyn_cast<BlockArgument>(product->getOperand(0));
  auto right = dyn_cast<BlockArgument>(product->getOperand(1));
  if (!left || !right || left.getOwner() != &formula ||
      right.getOwner() != &formula || !rowwise[left.getArgNumber()] ||
      !rowwise[right.getArgNumber()])
    return std::nullopt;
  return std::make_pair(left.getArgNumber(), right.getArgNumber());
}
} // namespace zkc::mathematical
