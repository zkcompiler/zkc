#ifndef ZKC_ANALYSIS_MATHEMATICAL_FACTS_H
#define ZKC_ANALYSIS_MATHEMATICAL_FACTS_H

#include "mlir/IR/Operation.h"
#include "zkc/Contracts/MathematicalFacts.h"
#include <memory>

namespace zkc {
/// Reusable observations of ONE immutable symbol closure. Construct on its
/// module/symbol owner (also through AnalysisManager), never on a function
/// whose evidence inspects sibling helpers. This borrows IR; it does not clone
/// it. Any mutation of the subject or inspected helpers requires invalidation
/// or clear() before further queries. Pass-manager invalidation is not a
/// substitute for clearing a view during a mutating pass.
///
/// Subjects require checked local structure and referenced ABIs. This is
/// optional fact extraction, not a substitute for closure/operation admission.
///
/// Query scopes and work are separate from this reusable information. Every
/// nested extraction and kernel query debits the caller's Work. Formation
/// import seeds identities and type extents without deriving every formal.
/// Helper observation charges depend on returned values, not unread body
/// operations or cache warmth; recursive result caches live within a query.
/// Formation assumptions come only from the original subjects' common helper,
/// never from a callee inspected to explain its result. Reached guards and
/// control-flow results supply no implicit assumptions; ordered admission is
/// neither removed nor moved by any query.
class MathematicalFactAnalysis {
public:
  explicit MathematicalFactAnalysis(mlir::Operation *symbolRoot);
  ~MathematicalFactAnalysis();
  MathematicalFactAnalysis(const MathematicalFactAnalysis &) = delete;
  MathematicalFactAnalysis &
  operator=(const MathematicalFactAnalysis &) = delete;

  /// Discard all borrowed helper observations after a mutation. The root must
  /// still exist. Reconstruct the analysis if the root itself changes.
  void clear();
  mlir::Operation *getRoot() const;
  /// Outermost symbol owner enclosing a subject, for transient consumers.
  static mlir::Operation *rootFor(mlir::Operation *subject);

  /// Exact SSA forwarding only. Constructors/equal shapes retain their own
  /// origin, including distinct invocations of the same constructor helper.
  facts::Result<mlir::Value> origin(mlir::Value, facts::Work &);
  /// Exact unsigned index literals and helper results; no wrapping arithmetic.
  facts::Result<uint64_t> integer(mlir::Value, facts::Work &);
  facts::Status equalExtent(mlir::Value left, unsigned leftAxis,
                            mlir::Value right, unsigned rightAxis,
                            facts::Work &);
  facts::Status bound(mlir::Value index, mlir::Value container, unsigned axis,
                      facts::Work &);
  facts::Result<uint64_t> extent(mlir::Value, unsigned axis, facts::Work &);
  /// Upper bounds are not exact extents and never establish strict bounds.
  facts::Result<facts::Cardinality> cardinality(mlir::Value, unsigned axis,
                                                facts::Work &);

private:
  struct Impl;
  std::unique_ptr<Impl> impl_;
};
} // namespace zkc
#endif
