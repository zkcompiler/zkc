#ifndef ZKC_TRANSFORMS_COMPUTATIONSELECTION_H
#define ZKC_TRANSFORMS_COMPUTATIONSELECTION_H
#include "ComputationEquations.h"
#include "MathematicalRecipes.h"
#include "zkc/Analysis/Computation.h"
#include "zkc/Transforms/MathematicalSelection.h"

namespace zkc::mathematical {
/// Implementation constraints are queried only at algorithm selection,
/// including the original mathematical invocations retained by structural
/// substitution. Callers reserve payload and numerical-call visits in scoped
/// equation work.
bool canReplacePayload(const finite::ComputationView &view);
bool canReplaceNestedContraction(const finite::ComputationView &view);

enum class RealizationKind {
  Ordered,
  Bilinear,
  NestedContraction,
  Reduction,
  CollectionSum,
  PointwiseReduction,
  Elementwise
};
struct SelectedReduction {
  const ReductionRecipe *recipe = nullptr;
  llvm::SmallVector<unsigned> inputs;
  std::optional<unsigned> selectedIndex;
  unsigned staticSourceInput = 0;
};
struct ComputationSelection {
  RealizationKind kind = RealizationKind::Ordered;
  finite::ComputationDiagnostic diagnostic;
  OptimizationStatus outcome() const { return diagnostic.outcome.status; }
  std::optional<finite::ComputationView> view;
  ComputationEquations equations;
  std::optional<NestedContraction> nested;
  std::optional<SelectedReduction> reduction;
  std::optional<SelectedReduction> collectionSum;
  // An actual collection/native-sum pair permits a summed expression even
  // when ordinary finite map selection is disabled. These are producer choices,
  // never premises supplied to the independent source/candidate reader.
  bool sumCollection = false;
  bool allowCollectionMap = true;
  const ReductionRecipe *pointwiseReduction = nullptr;
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
/// Reuse facts from an admitted immutable source closure. The result owns the
/// passed view: move it to transfer ownership, or copy it to share temporary
/// SSA storage. Rebuild after source edits/cloning; no persistent cache is
/// used. Source IR and enclosing views supplying borrowed SSA must outlive the
/// result. Recognition and selection debit work on every call;
/// structural/evidence work already spent producing the view is not repeated.
ComputationSelection
selectComputation(finite::ComputationView view,
                  MathematicalSelectionPolicy policy,
                  finite::ComputationWork &work,
                  const MathematicalRecipes &recipes = mathematicalRecipes());
struct NestedContractionSelection {
  /// Own any exact callback substitution referenced by the equation/witness.
  std::optional<finite::ComputationView> view;
  std::optional<NestedContraction> equation;
  const MatrixContractionRecipe *recipe = nullptr;
  finite::ComputationDiagnostic diagnostic;
  OptimizationStatus outcome() const { return diagnostic.outcome.status; }
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
                  const MathematicalRecipes &recipes = mathematicalRecipes(),
                  OptimizationOutcome *outcome = nullptr);
/// Describe a supported product map in scalar operand order. This does not
/// select a reduction target and is never evidence for candidate comparison.
std::optional<std::pair<unsigned, unsigned>>
selectMapProduct(mlir::Block &formula, llvm::ArrayRef<bool> rowwise,
                 OptimizationOutcome *outcome = nullptr);
/// Select a native-sum recipe for an admitted product map. The caller still
/// checks the sum's admission and implementation constraints. Product slots
/// retain scalar order until the recipe maps its operands.
std::optional<SelectedReduction>
selectMapSum(std::pair<unsigned, unsigned> product,
             const MathematicalRecipes &recipes = mathematicalRecipes(),
             OptimizationOutcome *outcome = nullptr);
} // namespace zkc::mathematical
#endif
