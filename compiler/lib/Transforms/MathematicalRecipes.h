#ifndef ZKC_TRANSFORMS_MATHEMATICALRECIPES_H
#define ZKC_TRANSFORMS_MATHEMATICALRECIPES_H
#include "zkc/Contracts/Operations.h"
#include <array>
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
/// Matrix axes are row (0) and column (1). Bilinear reduces both; Rows
/// preserves rows and reduces columns; Columns preserves columns and reduces
/// rows. Operand roles are matrix/left/right or matrix/vector, respectively.
enum class MatrixContractionForm { Bilinear, Rows, Columns };
struct MatrixContractionRecipe {
  MathematicalIdentity combine, term;
  MatrixContractionForm form;
  llvm::StringRef target, seedCombiner;
  std::array<unsigned, 3> operands;
  unsigned arity;
  protocol::ScalarIdentity emptyIdentity;
};
/// Immutable closed inventory view. An absent recipe never removes meaning.
struct MathematicalRecipes {
  llvm::ArrayRef<LaneRecipe> lanes;
  llvm::ArrayRef<ReductionRecipe> reductions;
  // Two-member aggregate overrides retain their original closed-inventory
  // meaning: newly introduced recipe families are absent unless supplied.
  llvm::ArrayRef<MatrixContractionRecipe> matrixContractions = {};
  const LaneRecipe *lane(MathematicalIdentity) const;
  const ReductionRecipe *reduction(MathematicalIdentity,
                                   std::optional<MathematicalIdentity>,
                                   ReductionForm) const;
  const MatrixContractionRecipe *matrixContraction(MathematicalIdentity,
                                                   MathematicalIdentity,
                                                   MatrixContractionForm) const;
};
const MathematicalRecipes &mathematicalRecipes();
} // namespace zkc::mathematical
#endif
