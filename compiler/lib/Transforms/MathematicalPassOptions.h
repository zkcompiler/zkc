#ifndef ZKC_TRANSFORMS_MATHEMATICAL_PASS_OPTIONS_H
#define ZKC_TRANSFORMS_MATHEMATICAL_PASS_OPTIONS_H

#include "mlir/Pass/Pass.h"
#include "zkc/Transforms/MathematicalSelection.h"

namespace zkc {
/// One option schema for passes that forward numerical selection. The value
/// stays invocation-local; copying a pass reconstructs options on its new
/// owner.
struct MathematicalPassOptions {
  mlir::Pass::Option<bool> finiteBulk;
  mlir::Pass::Option<bool> vectorReductionFusion;
  mlir::Pass::Option<bool> collectFoldFusion;
  mlir::Pass::Option<bool> calculationBatching;
  mlir::Pass::Option<NumericalExpressionMode> numericalExpressions;

  explicit MathematicalPassOptions(mlir::Pass &owner,
                                   MathematicalSelectionPolicy policy = {})
      : finiteBulk(owner, "optimize-finite", llvm::cl::init(true),
                   llvm::cl::desc("Select checked bulk finite realizations")),
        vectorReductionFusion(
            owner, "fuse-vector-reductions", llvm::cl::init(false),
            llvm::cl::desc("Fuse admitted vector reductions")),
        collectFoldFusion(
            owner, "fuse-collect-fold", llvm::cl::init(false),
            llvm::cl::desc(
                "Compose total collect and ordered fold traversals")),
        calculationBatching(
            owner, "calculation-batching", llvm::cl::init(true),
            llvm::cl::desc("Compute each calculation at its first demand")),
        numericalExpressions(
            owner, "numerical-expressions",
            llvm::cl::init(NumericalExpressionMode::PreferNative),
            llvm::cl::desc("Select the numerical expression representation"),
            llvm::cl::values(
                clEnumValN(NumericalExpressionMode::PreferNative,
                           "prefer-native",
                           "Prefer admitted native expression handlers"),
                clEnumValN(NumericalExpressionMode::VectorOnly, "vector-only",
                           "Use the vector expression representation"))) {
    set(policy);
  }
  void set(MathematicalSelectionPolicy policy) {
    finiteBulk = policy.finiteBulk;
    vectorReductionFusion = policy.vectorReductionFusion;
    collectFoldFusion = policy.collectFoldFusion;
    calculationBatching = policy.calculationBatching;
    numericalExpressions = policy.numericalExpressions;
  }
  MathematicalSelectionPolicy get() const {
    return {finiteBulk, vectorReductionFusion, collectFoldFusion,
            calculationBatching, numericalExpressions};
  }
};
} // namespace zkc
#endif
