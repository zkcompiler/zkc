#ifndef ZKC_TRANSFORMS_COMPUTATIONSELECTION_H
#define ZKC_TRANSFORMS_COMPUTATIONSELECTION_H
#include "ComputationEquations.h"
#include "MathematicalRecipes.h"
#include "zkc/Analysis/Computation.h"
#include "zkc/Transforms/MathematicalSelection.h"

namespace zkc::mathematical {
/// Implementation constraints are queried only at algorithm selection.
bool canReplacePayload(const finite::ComputationView &view);
bool canReplaceNestedContraction(const finite::ComputationView &view);

enum class RealizationKind { Ordered, Bilinear, Reduction, Elementwise };
/// Selection outcomes describe optional producer choices, never correspondence
/// evidence. AnalysisUnavailable includes unsupported structure or exhausted
/// analysis work; the structural API does not distinguish those cases.
enum class SelectionOutcome {
  Selected,
  AnalysisUnavailable,
  PolicyDisabled,
  UnsupportedEquation,
  ReplacementRestricted,
  MissingRecipe
};
llvm::StringRef describeSelectionOutcome(SelectionOutcome outcome);
struct SelectedReduction {
  const ReductionRecipe *recipe = nullptr;
  llvm::SmallVector<unsigned> inputs;
  std::optional<unsigned> selectedIndex;
  unsigned staticSourceInput = 0;
};
struct ComputationSelection {
  RealizationKind kind = RealizationKind::Ordered;
  SelectionOutcome outcome = SelectionOutcome::AnalysisUnavailable;
  std::optional<finite::ComputationView> view;
  ComputationEquations equations;
  std::optional<SelectedReduction> reduction;
  const MatrixContractionRecipe *matrix = nullptr;
};
/// Choose among installed logical algorithms; analysis supplies legal
/// structure and domain laws. Physical implementation selection remains later.
ComputationSelection
selectComputation(finite::Computation computation,
                  MathematicalSelectionPolicy policy,
                  const MathematicalRecipes &recipes = mathematicalRecipes());
ComputationSelection
selectComputation(finite::Computation computation,
                  MathematicalSelectionPolicy policy,
                  finite::ComputationWork &work,
                  const MathematicalRecipes &recipes = mathematicalRecipes());
struct NestedContractionSelection {
  std::optional<NestedContraction> equation;
  const MatrixContractionRecipe *recipe = nullptr;
  SelectionOutcome outcome = SelectionOutcome::UnsupportedEquation;
};
/// Recognize the nested equation even if an implementation pin or absent
/// matrix recipe prevents selection. The caller controls family policy.
NestedContractionSelection selectNestedContraction(
    const finite::ComputationView &view,
    const MathematicalRecipes &recipes = mathematicalRecipes());
NestedContractionSelection selectNestedContraction(
    const finite::ComputationView &view, finite::ComputationWork &work,
    const MathematicalRecipes &recipes = mathematicalRecipes());
/// Describe the same scalar/lane fragment for an explicit map. The caller has
/// independently admitted the complete helper closure, including dead work.
std::optional<Elementwise>
selectLaneFormula(mlir::Block &formula, llvm::ArrayRef<bool> rowwise,
                  const MathematicalRecipes &recipes = mathematicalRecipes());
/// Describe a supported product map in scalar operand order. This does not
/// select a reduction target and is never evidence for candidate comparison.
std::optional<std::pair<unsigned, unsigned>>
selectMapProduct(mlir::Block &formula, llvm::ArrayRef<bool> rowwise);
/// Select a native-sum recipe for an admitted product map. The caller still
/// checks the sum's admission and implementation constraints. Product slots
/// retain scalar order until the recipe maps its operands.
std::optional<SelectedReduction>
selectMapSum(std::pair<unsigned, unsigned> product,
             const MathematicalRecipes &recipes = mathematicalRecipes());
} // namespace zkc::mathematical
#endif
