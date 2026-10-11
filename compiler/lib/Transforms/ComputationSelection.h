#ifndef ZKC_TRANSFORMS_COMPUTATIONSELECTION_H
#define ZKC_TRANSFORMS_COMPUTATIONSELECTION_H
#include "MathematicalRecipes.h"
#include "zkc/Analysis/Computation.h"
#include "zkc/Transforms/MathematicalSelection.h"

namespace zkc::mathematical {
enum class RealizationKind { Ordered, Bilinear, Reduction, Elementwise };
struct SelectedReduction {
  const ReductionRecipe *recipe = nullptr;
  llvm::SmallVector<unsigned> inputs;
  std::optional<unsigned> selectedIndex;
  unsigned staticSourceInput = 0;
};
struct ComputationSelection {
  RealizationKind kind = RealizationKind::Ordered;
  std::optional<finite::ComputationView> view;
  std::optional<SelectedReduction> reduction;
};
/// Choose among installed logical algorithms; analysis supplies legal
/// structure and domain laws. Physical implementation selection remains later.
ComputationSelection
selectComputation(finite::Computation computation,
                  MathematicalSelectionPolicy policy,
                  const MathematicalRecipes &recipes = mathematicalRecipes());
/// Describe the same scalar/lane fragment for an explicit map. The caller has
/// independently admitted the complete helper closure, including dead work.
std::optional<finite::Elementwise>
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
