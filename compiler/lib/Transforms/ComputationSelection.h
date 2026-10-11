#ifndef ZKC_TRANSFORMS_COMPUTATIONSELECTION_H
#define ZKC_TRANSFORMS_COMPUTATIONSELECTION_H
#include "zkc/Analysis/Computation.h"
#include "zkc/Transforms/MathematicalSelection.h"

namespace zkc::mathematical {
enum class RealizationKind { Ordered, Bilinear, Reduction, Elementwise };
struct ComputationSelection {
  RealizationKind kind = RealizationKind::Ordered;
  std::optional<finite::ComputationView> view;
};
/// Choose among installed logical algorithms; analysis supplies legal
/// structure and domain laws. Physical implementation selection remains later.
ComputationSelection selectComputation(finite::Computation computation,
                                       MathematicalSelectionPolicy policy);
/// Describe the same scalar/lane fragment for an explicit map. The caller has
/// independently admitted the complete helper closure, including dead work.
std::optional<finite::Elementwise>
selectLaneFormula(mlir::Block &formula, llvm::ArrayRef<bool> rowwise);
/// A supported map followed by sum can be selected as a dot product. This is
/// optimizer classification only, never evidence for candidate comparison.
std::optional<std::pair<unsigned, unsigned>>
selectMapProduct(mlir::Block &formula, llvm::ArrayRef<bool> rowwise);
} // namespace zkc::mathematical
#endif
