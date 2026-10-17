#include "ComputationSelection.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
bool laneRecipesAvailable(Block &body, const Elementwise &formula,
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
selectReduction(const Reduction &equation, const MathematicalRecipes &recipes) {
  auto form = equation.matrixOperand
                  ? (equation.matrixAccess == finite::AccessKind::MatrixRow
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
bool canReplacePayload(const finite::ComputationView &view) {
  return llvm::all_of(view.payload,
                      [](Operation *op) { return finite::replaceable(op); });
}
bool canReplaceNestedContraction(const finite::ComputationView &view) {
  if (view.nested.size() != 1 || !canReplacePayload(view.nested.front()))
    return false;
  Operation *call = view.nested.front().occurrence;
  return llvm::all_of(view.payload, [&](Operation *op) {
    return op == call || finite::replaceable(op);
  });
}
ComputationSelection selectComputation(finite::Computation computation,
                                       MathematicalSelectionPolicy policy,
                                       const MathematicalRecipes &recipes) {
  finite::ComputationWork work;
  return selectComputation(computation, policy, work, recipes);
}
ComputationSelection selectComputation(finite::Computation computation,
                                       MathematicalSelectionPolicy policy,
                                       finite::ComputationWork &work,
                                       const MathematicalRecipes &recipes) {
  ComputationSelection selection;
  selection.view =
      finite::analyzeComputation(computation, work, &selection.diagnostic);
  if (!selection.view) {
    return selection;
  }
  selection.equations =
      matchComputation(*selection.view, work, &selection.diagnostic);
  if (!policy.finiteBulk) {
    selection.diagnostic.outcome = {OptimizationStatus::PolicyDisabled,
                                    OptimizationReason::Policy};
    return selection;
  }
  if (!selection.equations.bilinear && !selection.equations.reduction &&
      !selection.equations.pointwiseReduction &&
      !selection.equations.elementwise) {
    return selection;
  }
  // Replacement and recipe checks also inspect the complete payload. Reserve
  // their optional work before walking it; ordered emission has its own budget.
  if (!finite::consumeComputationWork(
          work.equations, selection.view->payload.size() + 1,
          WorkOwner::Equations, &selection.diagnostic.outcome)) {
    return selection;
  }
  if (!canReplacePayload(*selection.view)) {
    selection.diagnostic.outcome = {OptimizationStatus::ReplacementRestricted,
                                    OptimizationReason::Replacement};
    return selection;
  }
  if (selection.equations.bilinear) {
    selection.matrix = recipes.matrixContraction(
        MathematicalIdentity::FieldAdd, MathematicalIdentity::FieldMultiply,
        MatrixContractionForm::Bilinear);
    if (selection.matrix)
      selection.kind = RealizationKind::Bilinear;
  } else if (selection.equations.reduction) {
    selection.reduction =
        selectReduction(*selection.equations.reduction, recipes);
    if (selection.reduction)
      selection.kind = RealizationKind::Reduction;
  } else if (selection.equations.pointwiseReduction) {
    const auto &equation = *selection.equations.pointwiseReduction;
    if (laneRecipesAvailable(*selection.view->callbackBody, equation.formula,
                             recipes)) {
      selection.pointwiseReduction =
          recipes.reduction(equation.combine, {}, ReductionForm::Direct);
      if (selection.pointwiseReduction)
        selection.kind = RealizationKind::PointwiseReduction;
    }
  } else if (selection.equations.elementwise &&
             laneRecipesAvailable(*selection.view->callbackBody,
                                  *selection.equations.elementwise, recipes))
    selection.kind = RealizationKind::Elementwise;
  selection.diagnostic.outcome =
      selection.kind == RealizationKind::Ordered
          ? OptimizationOutcome{OptimizationStatus::MissingRecipe,
                                OptimizationReason::Recipe}
          : OptimizationOutcome::success();
  return selection;
}
NestedContractionSelection
selectNestedContraction(const finite::ComputationView &view,
                        const MathematicalRecipes &recipes) {
  finite::ComputationWork work;
  return selectNestedContraction(view, work, recipes);
}
NestedContractionSelection
selectNestedContraction(const finite::ComputationView &view,
                        finite::ComputationWork &work,
                        const MathematicalRecipes &recipes) {
  NestedContractionSelection selection;
  selection.equation =
      matchNestedContraction(view, work, &selection.diagnostic);
  if (!selection.equation) {
    return selection;
  }
  if (!finite::consumeComputationWork(
          work.equations,
          view.payload.size() + view.nested.front().payload.size() + 1,
          WorkOwner::Equations, &selection.diagnostic.outcome)) {
    return selection;
  }
  if (!canReplaceNestedContraction(view)) {
    selection.diagnostic.outcome = {OptimizationStatus::ReplacementRestricted,
                                    OptimizationReason::Replacement};
    return selection;
  }
  selection.recipe = recipes.matrixContraction(
      MathematicalIdentity::FieldAdd, MathematicalIdentity::FieldMultiply,
      selection.equation->axis == 0 ? MatrixContractionForm::Rows
                                    : MatrixContractionForm::Columns);
  selection.diagnostic.outcome =
      selection.recipe ? OptimizationOutcome::success()
                       : OptimizationOutcome{OptimizationStatus::MissingRecipe,
                                             OptimizationReason::Recipe};
  return selection;
}
std::optional<Elementwise> selectLaneFormula(Block &formula,
                                             ArrayRef<bool> rowwise,
                                             const MathematicalRecipes &recipes,
                                             OptimizationOutcome *outcome) {
  if (outcome)
    *outcome = {OptimizationStatus::Unsupported,
                OptimizationReason::LaneFormula};
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
  auto result = matchLaneFormula(formula, field, lanes);
  if (!result)
    return std::nullopt;
  if (!laneRecipesAvailable(formula, *result, recipes)) {
    if (outcome)
      *outcome = {OptimizationStatus::MissingRecipe,
                  OptimizationReason::Recipe};
    return std::nullopt;
  }
  if (outcome)
    *outcome = OptimizationOutcome::success();
  return result;
}
std::optional<std::pair<unsigned, unsigned>>
selectMapProduct(Block &formula, ArrayRef<bool> rowwise,
                 OptimizationOutcome *outcome) {
  if (outcome)
    *outcome = {OptimizationStatus::Unsupported, OptimizationReason::Equation};
  if (formula.empty())
    return std::nullopt;
  if (!llvm::all_of(formula.without_terminator(),
                    [](Operation &op) { return finite::replaceable(&op); })) {
    if (outcome)
      *outcome = {OptimizationStatus::ReplacementRestricted,
                  OptimizationReason::Replacement};
    return std::nullopt;
  }
  auto result = matchMapProduct(formula, rowwise);
  if (result && outcome)
    *outcome = OptimizationOutcome::success();
  return result;
}
std::optional<SelectedReduction>
selectMapSum(std::pair<unsigned, unsigned> product,
             const MathematicalRecipes &recipes, OptimizationOutcome *outcome) {
  Reduction equation;
  equation.combine = MathematicalIdentity::FieldAdd;
  equation.termIdentity = MathematicalIdentity::FieldMultiply;
  equation.inputs = {product.first, product.second};
  auto result = selectReduction(equation, recipes);
  if (outcome)
    *outcome = result ? OptimizationOutcome::success()
                      : OptimizationOutcome{OptimizationStatus::MissingRecipe,
                                            OptimizationReason::Recipe};
  return result;
}
} // namespace zkc::mathematical
