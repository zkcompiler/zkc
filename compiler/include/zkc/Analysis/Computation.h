#ifndef ZKC_ANALYSIS_COMPUTATION_H
#define ZKC_ANALYSIS_COMPUTATION_H

#include "zkc/Analysis/ComputationMeaning.h"
#include "zkc/Analysis/ComputationWork.h"
#include "zkc/Analysis/Finite.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseMap.h"
#include <memory>
#include <optional>

namespace zkc {
class MathematicalFactAnalysis;
}
namespace zkc::finite {
struct ComputationBody;
/// Views borrow admitted source IR and may own exact temporary SSA copies.
/// Recompute after source changes or cloning. No symbolic expressions are
/// added.
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
  /// Existing helper container and explicit index SSA, where present.
  mlir::Value container;
  llvm::SmallVector<mlir::Value> indices;
  /// Positions in ComputationView.axes; equal extents never merge identities.
  llvm::SmallVector<unsigned> axes;
};
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
  unsigned axis = 0;
};
struct AxisIdentity {
  /// Root invocation followed by nested call occurrences, not symbol names.
  llvm::SmallVector<mlir::Operation *> occurrence;
  mlir::Operation *constructor = nullptr;
  /// Child operand positions from the returned descriptor to this leaf.
  /// Reusing one descriptor twice in a product creates distinct axes.
  llvm::SmallVector<unsigned> path;
  unsigned coordinate = 0;
  bool operator==(const AxisIdentity &other) const {
    return occurrence == other.occurrence && constructor == other.constructor &&
           path == other.path && coordinate == other.coordinate;
  }
  bool operator!=(const AxisIdentity &other) const { return !(*this == other); }
};
struct Axis {
  AxisIdentity identity;
  mlir::Value container;
  std::optional<unsigned> containerAxis;
};
struct InputReference {
  unsigned input = 0;
  mlir::Value formal;
  /// Empty for a declaration without a call occurrence.
  mlir::Value actual;
  /// Domain arguments only; seeds and extra captures have no domain formal.
  mlir::Value domainFormal;
  /// Actual after enclosing invariant capture substitutions. State is never
  /// substituted by its initial seed; enclosing item SSA stays
  /// occurrence-bound.
  mlir::Value resolved;
  bool state = false;
};
struct ComputationEnvironment {
  /// Signature order, shared by structural access and equation composition.
  llvm::SmallVector<InputReference> inputs;
  std::optional<unsigned> inputPosition(mlir::Value formal) const;
  mlir::Value actualInput(unsigned input) const;
  mlir::Value resolveCapture(mlir::Value value) const;
};
struct ArgumentReference {
  mlir::Value formal, source;
};
struct ResultReference {
  unsigned output = 0;
  mlir::Value yielded;
  /// Empty on a declaration. A collect yield is an item of this collection.
  mlir::Value actual;
  /// Exact zero-trip initial state at a call; absent on declarations/collect.
  mlir::Value initial;
  /// Preserves zero-trip identity even when analyzing a declaration.
  std::optional<unsigned> seedInput;
  mlir::Type type;
  /// A collect without a predicate has the returned domain's cardinality.
  /// Filtering provides no exact cardinality fact.
  std::optional<unsigned> cardinality;
  /// Actual original callback return coordinate, before exact call
  /// substitution.
  mlir::Value sourceYielded;
};
/// Diagnostic references have the same borrowed lifetime as a view.
struct ComputationDiagnostic {
  OptimizationOutcome outcome;
  mlir::Operation *subject = nullptr;
  mlir::Value access;
  llvm::SmallVector<mlir::Operation *> occurrencePath = {};
};
struct ComputationView {
  Computation computation;
  /// Temporary call/pack substitution and a checked mathematical view of
  /// eligible scoped primitives in a private standard func.func. Original
  /// executable primitives may remain as typed uninterpreted calls with source
  /// associations, including their bindings and pins. These calls have no
  /// mathematical facet; this storage does not establish purity or change the
  /// source callback ABI. No arithmetic or polynomial normalization is
  /// performed. Copies share the owning lifetime; the original callback and its
  /// symbol closure stay immutable.
  std::shared_ptr<ComputationBody> numericalBody;
  /// Original callback block or the owned standard-function body above.
  mlir::Block *callbackBody = nullptr;
  /// Recover the actual source instruction from a temporary payload occurrence.
  mlir::Operation *sourceOperation(mlir::Operation *operation) const;
  /// Original numerical requests read through by exact substitution, in
  /// expansion order. Repeated visits to a shared call site remain separate
  /// entries. Borrows source IR under the view's lifetime contract; selection
  /// must query these calls rather than infer permission from substituted
  /// mathematics.
  llvm::ArrayRef<mlir::Operation *> numericalCalls() const;
  /// Exact substituted SSA for an original callback argument or result.
  mlir::Value callbackValue(mlir::Value source) const;
  /// The actual nested call, or the total operation/declaration at the root.
  mlir::Operation *occurrence = nullptr;
  llvm::SmallVector<mlir::Operation *> occurrencePath;
  ComputationEnvironment environment;
  /// Constructor SSA order is also eager admission order. Unused domain
  /// constructors are retained; nested admission belongs to each nested view.
  llvm::SmallVector<Iteration> iteration;
  unsigned root = 0;
  /// Helper item order, retaining each leaf's constructor provenance.
  llvm::SmallVector<IterationItem> items;
  llvm::SmallVector<Axis> axes;
  llvm::SmallVector<mlir::Operation *> admission;
  llvm::SmallVector<InputReference> seeds, captures;
  llvm::SmallVector<mlir::Operation *> payload;
  /// Actual return or stop. A stop has no successful yielded results.
  mlir::Operation *terminator = nullptr;
  /// Predicate arguments map to helper item/capture formals, excluding state.
  llvm::SmallVector<ArgumentReference> predicateArguments;
  llvm::SmallVector<mlir::Operation *> predicatePayload;
  llvm::SmallVector<mlir::Value> predicateResults;
  mlir::Operation *predicateTerminator = nullptr;
  /// Complete supported access inventory, independent of equation selection.
  /// Unsupported operations remain in payload and gain no access fact.
  llvm::SmallVector<Access> accesses;
  /// Sparse unavailable evidence; a successful view need not have all accesses.
  llvm::SmallVector<ComputationDiagnostic> accessDeclines;
  std::vector<ComputationView> nested;
  llvm::SmallVector<mlir::Value> results;
  llvm::SmallVector<ResultReference> resultMappings;
  mlir::Value result;
};
/// Read-only, invocation-scoped structural analysis. The caller must already
/// have admitted the complete helper closure. Unknown payloads remain opaque
/// and ordered; optional recognition failure does not reject that fallback.
/// A bounded structural walk refuses cycles/budget exhaustion without mutation.
std::optional<ComputationView> analyzeComputation(Computation computation,
                                                  unsigned budget = 100000);
std::optional<ComputationView>
analyzeComputation(Computation computation, ComputationWork &work,
                   ComputationDiagnostic *diagnostic = nullptr);
/// Reuse only facts from this immutable source closure. Work and diagnostics
/// belong to this invocation, including when the analysis is already warm.
std::optional<ComputationView>
analyzeComputation(Computation, ComputationWork &, MathematicalFactAnalysis &,
                   ComputationDiagnostic *diagnostic = nullptr);
} // namespace zkc::finite
#endif
