#include "ComputationSelection.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
bool laneRecipesAvailable(Block &body, const finite::Elementwise &formula,
                          const MathematicalRecipes &recipes) {
  for (Operation &op : body.without_terminator()) {
    const auto *meaning = finite::semantics(&op);
    if (!meaning || !finite::replaceable(&op))
      return false;
    if (meaning->identity != MathematicalIdentity::FieldConstant &&
        !formula.lookups.contains(op.getResult(0)) &&
        !recipes.lane(meaning->identity))
      return false;
  }
  return true;
}
std::optional<SelectedReduction>
selectReduction(const finite::Reduction &equation,
                const MathematicalRecipes &recipes) {
  auto form = equation.matrixOperand
                  ? (equation.demand == finite::DemandKind::MatrixRow
                         ? ReductionForm::MatrixRow
                         : ReductionForm::MatrixColumn)
                  : (equation.termIdentity ? ReductionForm::Contraction
                                           : ReductionForm::Direct);
  const auto *recipe =
      recipes.reduction(equation.combine, equation.termIdentity, form);
  if (!recipe)
    return std::nullopt;
  SelectedReduction result;
  result.recipe = recipe;
  result.selectedIndex = equation.selectedIndex;
  auto sourcePosition = [&](unsigned operand) {
    return equation.matrixOperand ? (operand == 0 ? *equation.matrixOperand
                                                  : 1 - *equation.matrixOperand)
                                  : operand;
  };
  result.inputs.push_back(equation.inputs[sourcePosition(recipe->first)]);
  if (form != ReductionForm::Direct)
    result.inputs.push_back(equation.inputs[sourcePosition(recipe->second)]);
  result.staticSourceInput =
      equation.inputs[sourcePosition(recipe->staticSourceOperand)];
  return result;
}
} // namespace
ComputationSelection selectComputation(finite::Computation computation,
                                       MathematicalSelectionPolicy policy,
                                       const MathematicalRecipes &recipes) {
  ComputationSelection selection;
  selection.view = finite::analyzeComputation(computation);
  if (!selection.view || !policy.finiteBulk || !selection.view->replaceable)
    return selection;
  if (selection.view->bilinear)
    selection.kind = RealizationKind::Bilinear;
  else if (selection.view->reduction) {
    selection.reduction = selectReduction(*selection.view->reduction, recipes);
    if (selection.reduction)
      selection.kind = RealizationKind::Reduction;
  } else if (selection.view->elementwise &&
             laneRecipesAvailable(computation.helper->getRegion(0).front(),
                                  *selection.view->elementwise, recipes))
    selection.kind = RealizationKind::Elementwise;
  return selection;
}
std::optional<finite::Elementwise>
selectLaneFormula(Block &formula, ArrayRef<bool> rowwise,
                  const MathematicalRecipes &recipes) {
  if (formula.empty() || formula.getNumArguments() != rowwise.size() ||
      formula.back().getNumOperands() != 1)
    return std::nullopt;
  Type field = formula.back().getOperand(0).getType();
  if (!isa<algebra::FieldType>(field))
    return std::nullopt;
  SmallVector<Value> lanes;
  for (auto [i, argument] : enumerate(formula.getArguments()))
    if (rowwise[i])
      lanes.push_back(argument);
  auto result = finite::analyzeLaneFormula(formula, field, lanes);
  return result && laneRecipesAvailable(formula, *result, recipes)
             ? result
             : std::nullopt;
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
std::optional<SelectedReduction>
selectMapSum(std::pair<unsigned, unsigned> product,
             const MathematicalRecipes &recipes) {
  finite::Reduction equation;
  equation.combine = MathematicalIdentity::FieldAdd;
  equation.termIdentity = MathematicalIdentity::FieldMultiply;
  equation.inputs = {product.first, product.second};
  return selectReduction(equation, recipes);
}
} // namespace zkc::mathematical
