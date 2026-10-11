#ifndef ZKC_TRANSFORMS_FINITESUPPORT_H
#define ZKC_TRANSFORMS_FINITESUPPORT_H
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include <optional>
namespace zkc::finite {
struct Collection {
  std::string family;
  std::vector<std::string> arguments;
  mlir::Type element;
};
Collection collection(mlir::Type type);
struct Bilinear {
  mlir::Value matrix, left, right;
};
std::optional<Bilinear> recognizeBilinear(Computation computation);
struct Reduction {
  std::string kernel, combine;
  // Item positions, in native kernel order; matrix contraction also carries
  // the selected matrix view rather than materializing it.
  llvm::SmallVector<unsigned> items;
};
mlir::StringRef arithmetic(mlir::Operation *operation);
void domainLeaves(mlir::Value descriptor,
                  llvm::SmallVectorImpl<mlir::Operation *> &out);
std::optional<std::string> fieldConstant(mlir::Operation *operation);
// The plan classifies existing SSA values; it does not represent an expression
// language. All ordinary helper instructions are read before this query
// succeeds.
enum class FormulaMode { Scalar, Rows, Index, Container, Unused };
struct Elementwise {
  llvm::DenseMap<mlir::Value, FormulaMode> modes;
  llvm::DenseMap<mlir::Value, mlir::Value> lookups;
};
std::optional<Elementwise> recognizeElementwise(Computation computation);
std::optional<Reduction> recognizeReduction(Computation computation);
} // namespace zkc::finite
#endif
