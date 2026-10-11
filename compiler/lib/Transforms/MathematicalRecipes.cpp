#include "MathematicalRecipes.h"
namespace zkc::mathematical {
namespace {
#include "MathematicalRecipes.inc"
} // namespace
const MathematicalRecipes &mathematicalRecipes() {
  static const MathematicalRecipes recipes{laneRecipes, reductionRecipes,
                                           matrixContractionRecipes};
  return recipes;
}
const LaneRecipe *
MathematicalRecipes::lane(MathematicalIdentity identity) const {
  for (const auto &recipe : lanes)
    if (recipe.identity == identity)
      return &recipe;
  return nullptr;
}
const ReductionRecipe *
MathematicalRecipes::reduction(MathematicalIdentity combine,
                               std::optional<MathematicalIdentity> term,
                               ReductionForm form) const {
  for (const auto &recipe : reductions)
    if (recipe.combine == combine && recipe.term == term && recipe.form == form)
      return &recipe;
  return nullptr;
}
const MatrixContractionRecipe *
MathematicalRecipes::matrixContraction(MathematicalIdentity combine,
                                       MathematicalIdentity term,
                                       MatrixContractionForm form) const {
  for (const auto &recipe : matrixContractions)
    if (recipe.combine == combine && recipe.term == term && recipe.form == form)
      return &recipe;
  return nullptr;
}
} // namespace zkc::mathematical
