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

/// Exact logical meaning, including explicitly constrained implementations.
/// Unknown attributes and mismatched nominal ports have no semantic facet.
/// No serialized analysis attribute is consulted.
const protocol::ComputationContract *semantics(mlir::Operation *operation);
/// Meaning alone does not authorize rebinding an explicit implementation.
bool replaceable(mlir::Operation *operation);
std::optional<std::string> fieldConstant(mlir::Operation *operation);

/// All references below borrow the current, admitted IR. Recompute after IR
/// changes or cloning. These views describe existing values, never expressions.
enum class DemandKind { Scalar, MatrixRow, MatrixColumn, Collection };
enum class AccessKind { Element, Indexed, MatrixRow, MatrixColumn, MatrixCell };
struct Access {
  AccessKind kind = AccessKind::Element;
  /// Position in Computation.signature inputs, including captured containers.
  unsigned input = 0;
  /// Enumerated item whose position drives the access (also for indexed reads).
  unsigned item = 0;
  std::optional<unsigned> selectedIndex;
  mlir::Value value;
  mlir::Operation *operation = nullptr;
  /// Column item for a cell with two enumerated coordinates; item is its row.
  std::optional<unsigned> columnItem;
};
struct Reduction {
  MathematicalIdentity combine;
  std::optional<MathematicalIdentity> termIdentity;
  /// Inputs in scalar term operand order, before any native permutation.
  llvm::SmallVector<unsigned> inputs;
  std::optional<unsigned> selectedIndex;
  /// Position in inputs/accesses with the matrix role. Other inputs retain
  /// source order, including the group/scalar order of a module action.
  std::optional<unsigned> matrixOperand;
  DemandKind demand = DemandKind::Scalar;
  llvm::SmallVector<Access> accesses;
  mlir::Value accumulator, term;
  mlir::Operation *combiner = nullptr;
};
struct Bilinear {
  mlir::Value matrix, left, right;
};

struct Elementwise {
  /// Scalar indexed reads that the lane emitter replaces by their container.
  llvm::DenseMap<mlir::Value, mlir::Value> lookups;
};
/// Common lane classification for an existing scalar SSA block. Every
/// instruction is inspected, including unused instructions. indices maps an
/// enumerated index to the exact captured container it traverses. Other exact
/// field arguments are uniform; the returned view retains only emitter inputs.
std::optional<Elementwise>
analyzeLaneFormula(mlir::Block &body, mlir::Type field,
                   mlir::ValueRange laneArguments,
                   const llvm::DenseMap<mlir::Value, mlir::Value> &indices =
                       llvm::DenseMap<mlir::Value, mlir::Value>());

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
struct IterationItem {
  unsigned iteration = 0;
  mlir::Value formal;
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
  /// Helper item order, retaining each leaf's constructor provenance.
  llvm::SmallVector<IterationItem> items;
  llvm::SmallVector<mlir::Operation *> admission;
  llvm::SmallVector<InputReference> seeds, captures;
  llvm::SmallVector<mlir::Operation *> payload;
  /// Complete supported access inventory, independent of equation selection.
  /// Unsupported operations remain in payload and gain no access fact.
  llvm::SmallVector<Access> accesses;
  std::vector<ComputationView> nested;
  llvm::SmallVector<mlir::Value> results;
  mlir::Value result;
  DemandKind demand = DemandKind::Scalar;
  /// Equation recognition is independent of this occurrence's permission to
  /// replace physical constraints. Selection must check the latter separately.
  bool replaceable = true;
  std::optional<Reduction> reduction;
  std::optional<Elementwise> elementwise;
  std::optional<Bilinear> bilinear;
};
/// Read-only, invocation-scoped structural analysis. The caller must already
/// have admitted the complete helper closure. Unknown payloads remain opaque
/// and ordered; optional recognition failure does not reject that fallback.
/// A bounded structural walk refuses cycles/budget exhaustion without mutation.
std::optional<ComputationView> analyzeComputation(Computation computation,
                                                  unsigned budget = 100000);
} // namespace zkc::finite
#endif
