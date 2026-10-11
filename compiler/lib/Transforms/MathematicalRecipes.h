#ifndef ZKC_TRANSFORMS_MATHEMATICALRECIPES_H
#define ZKC_TRANSFORMS_MATHEMATICALRECIPES_H
#include "zkc/Contracts/Operations.h"
namespace zkc::mathematical {
struct LaneRecipe {
  MathematicalIdentity identity;
  llvm::StringRef scalar, rows, mixed;
  unsigned scalarOperand, first, second;
};
enum class ReductionForm { Direct, Contraction, MatrixRow, MatrixColumn };
struct ReductionRecipe {
  MathematicalIdentity combine;
  std::optional<MathematicalIdentity> term;
  ReductionForm form;
  llvm::StringRef target, combiner;
  unsigned first, second, staticSourceOperand;
  protocol::ScalarIdentity emptyIdentity;
};
/// Immutable closed inventory view. An absent recipe never removes meaning.
struct MathematicalRecipes {
  llvm::ArrayRef<LaneRecipe> lanes;
  llvm::ArrayRef<ReductionRecipe> reductions;
  const LaneRecipe *lane(MathematicalIdentity) const;
  const ReductionRecipe *reduction(MathematicalIdentity,
                                   std::optional<MathematicalIdentity>,
                                   ReductionForm) const;
};
const MathematicalRecipes &mathematicalRecipes();
} // namespace zkc::mathematical
#endif
