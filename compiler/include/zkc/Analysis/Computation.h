#ifndef ZKC_ANALYSIS_COMPUTATION_H
#define ZKC_ANALYSIS_COMPUTATION_H

#include "zkc/Analysis/Finite.h"
#include "zkc/Contracts/Operations.h"
#include "llvm/ADT/DenseMap.h"
#include <optional>

namespace zkc::finite {
struct Collection {
  std::string family;
  std::vector<std::string> arguments;
  mlir::Type element;
};
Collection collection(mlir::Type type);

/// An admitted installed scalar/access equation for this exact operation.
/// Explicit implementations, unknown attributes and mismatched nominal ports
/// have no replacement facet. No serialized analysis attribute is consulted.
const protocol::ComputationContract *semantics(mlir::Operation *operation);
std::optional<std::string> fieldConstant(mlir::Operation *operation);
void domainLeaves(mlir::Value descriptor,
                  llvm::SmallVectorImpl<mlir::Operation *> &out);

/// All references below borrow the current, admitted IR. Recompute after IR
/// changes or cloning. These views describe existing values, never expressions.
enum class DemandKind { Scalar, MatrixRow, MatrixColumn, Collection };
enum class AccessKind { Element, Indexed, MatrixRow, MatrixColumn };
struct Access {
  AccessKind kind = AccessKind::Element;
  /// Position in Computation.signature inputs, including captured containers.
  unsigned input = 0;
  /// Enumerated item whose position drives the access (also for indexed reads).
  unsigned item = 0;
  std::optional<unsigned> selectedIndex;
  mlir::Value value;
  mlir::Operation *operation = nullptr;
};
struct Reduction {
  std::string kernel, combine;
  /// Native kernel inputs as positions in Computation.signature inputs.
  /// A row/column contraction appends selectedIndex after these inputs.
  llvm::SmallVector<unsigned> inputs;
  std::optional<unsigned> selectedIndex;
  DemandKind demand = DemandKind::Scalar;
  llvm::SmallVector<Access> accesses;
  mlir::Value accumulator, term;
  mlir::Operation *combiner = nullptr;
};
struct Bilinear {
  mlir::Value matrix, left, right;
};

// Shared classification of actual scalar and row SSA values.
enum class FormulaMode { Scalar, Rows, Index, Container, Unused };
struct Elementwise {
  llvm::DenseMap<mlir::Value, FormulaMode> modes;
  llvm::DenseMap<mlir::Value, mlir::Value> lookups;
};
/// Common lane classification for an existing scalar SSA block. Every
/// instruction is inspected, including unused instructions. indices maps an
/// enumerated index to the exact captured container it traverses.
std::optional<Elementwise>
recognizeFormula(mlir::Block &body, mlir::Type field,
                 llvm::DenseMap<mlir::Value, FormulaMode> modes,
                 const llvm::DenseMap<mlir::Value, mlir::Value> &indices =
                     llvm::DenseMap<mlir::Value, mlir::Value>());
std::optional<Elementwise> recognizeElementwise(Computation computation);
std::optional<Reduction> recognizeReduction(Computation computation);
std::optional<Bilinear> recognizeBilinear(Computation computation);

enum class IterationKind {
  Elements,
  Indices,
  MatrixRow,
  MatrixColumn,
  Coordinates,
  Range,
  Zip,
  Product
};
struct Iteration {
  mlir::Operation *operation = nullptr;
  mlir::Value descriptor;
  IterationKind kind;
  llvm::SmallVector<unsigned> children;
};
struct InputReference {
  unsigned input = 0;
  mlir::Value formal;
  /// Empty for a declaration without a call occurrence.
  mlir::Value actual;
};
struct ComputationView {
  Computation computation;
  /// The actual nested call, or the total operation/declaration at the root.
  mlir::Operation *occurrence = nullptr;
  /// Constructor SSA order is also eager admission order. Unused domain
  /// constructors are retained; nested admission belongs to each nested view.
  llvm::SmallVector<Iteration> iteration;
  unsigned root = 0;
  llvm::SmallVector<mlir::Operation *> admission;
  llvm::SmallVector<InputReference> seeds, captures;
  llvm::SmallVector<mlir::Operation *> payload;
  llvm::SmallVector<Access> accesses;
  std::vector<ComputationView> nested;
  llvm::SmallVector<mlir::Value> results;
  mlir::Value result;
  DemandKind demand = DemandKind::Scalar;
  std::optional<Reduction> reduction;
  std::optional<Elementwise> elementwise;
};
/// Read-only, invocation-scoped structural analysis. The caller must already
/// have admitted the complete helper closure. Unknown payloads remain opaque
/// and ordered; optional recognition failure does not reject that fallback.
/// A bounded structural walk refuses cycles/budget exhaustion without mutation.
std::optional<ComputationView> analyzeComputation(Computation computation,
                                                  unsigned budget = 100000);
} // namespace zkc::finite
#endif
