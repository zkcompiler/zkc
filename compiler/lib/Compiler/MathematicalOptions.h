#ifndef ZKC_COMPILER_MATHEMATICALOPTIONS_H
#define ZKC_COMPILER_MATHEMATICALOPTIONS_H
#include "mlir/Pass/PassRegistry.h"
#include "zkc/Transforms/MathematicalSelection.h"
namespace zkc::detail {
template <typename Derived>
struct MathematicalOptions : mlir::PassPipelineOptions<Derived> {
  using Base = mlir::PassPipelineOptions<Derived>;
  typename Base::template Option<bool> optimizeFinite{
      *this, "optimize-finite", llvm::cl::init(true),
      llvm::cl::desc("Select checked bulk finite realizations")};
  typename Base::template Option<bool> fuseVectorReductions{
      *this, "fuse-vector-reductions", llvm::cl::init(false),
      llvm::cl::desc("Fuse admitted vector maps and reductions")};
  typename Base::template Option<bool> fuseCollectFold{
      *this, "fuse-collect-fold", llvm::cl::init(false),
      llvm::cl::desc("Compose total collect and ordered fold traversals")};
  typename Base::template Option<bool> calculationBatching{
      *this, "calculation-batching", llvm::cl::init(true),
      llvm::cl::desc("Compute each calculation at its first demand")};
  typename Base::template Option<NumericalExpressionMode> numericalExpressions{
      *this, "numerical-expressions",
      llvm::cl::init(NumericalExpressionMode::PreferNative),
      llvm::cl::desc("Select the numerical expression representation"),
      llvm::cl::values(
          clEnumValN(NumericalExpressionMode::PreferNative, "prefer-native",
                     "Prefer admitted native expression handlers"),
          clEnumValN(NumericalExpressionMode::VectorOnly, "vector-only",
                     "Use the vector expression representation"))};
  MathematicalSelectionPolicy mathematics() const {
    return {optimizeFinite, fuseVectorReductions, fuseCollectFold,
            calculationBatching, numericalExpressions};
  }
};
} // namespace zkc::detail
#endif
