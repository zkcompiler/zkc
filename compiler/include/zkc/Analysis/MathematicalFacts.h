#ifndef ZKC_ANALYSIS_MATHEMATICAL_FACTS_H
#define ZKC_ANALYSIS_MATHEMATICAL_FACTS_H

#include "mlir/IR/Operation.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/Pass/AnalysisManager.h"
#include "zkc/Contracts/MathematicalFacts.h"
#include <memory>

namespace zkc {
/// Symbol lookup for a single immutable closure. The analysis is owned at the
/// enclosing module, not cached on a callable that can inspect its siblings.
/// This holds no admission result or work allowance.
class SymbolClosureAnalysis {
  mlir::Operation *root;
  std::unique_ptr<mlir::SymbolTableCollection> symbols;

public:
  explicit SymbolClosureAnalysis(mlir::Operation *root);
  mlir::Operation *lookup(mlir::Operation *, mlir::SymbolRefAttr);
  void clear();
};
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
/// nested extraction and kernel query debits the caller's Work. Query depth
/// starts at the caller's consumed interpretation depth (zero at a root);
/// nested domain adapters must preserve it across the leaf boundary. Formation
/// import seeds identities and type extents without deriving every formal.
/// Helper observation charges depend on returned values, not unread body
/// operations or cache warmth; recursive result caches live within a query.
/// Formation assumptions come only from the original subjects' common helper,
/// never from a callee inspected to explain its result. Reached guards and
/// control-flow results supply no implicit assumptions; ordered admission is
/// neither removed nor moved by any query.
/// CFG function premises refer to entry arguments, never same-numbered
/// successor block arguments. Pure helper-result extraction remains restricted
/// to admitted single-block mathematical bodies.
/// A unique successful dispatch of an index.constant binding preserves that
/// exact literal; arbitrary joins and reached tests supply no literal evidence.
class MathematicalFactAnalysis {
public:
  explicit MathematicalFactAnalysis(mlir::Operation *symbolRoot);
  MathematicalFactAnalysis(mlir::Operation *symbolRoot,
                           mlir::AnalysisManager &);
  bool isInvalidated(const mlir::AnalysisManager::PreservedAnalyses &);
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
  facts::Result<mlir::Value> origin(mlir::Value, facts::Work &,
                                    unsigned depth = 0);
  /// Exact unsigned index literals and helper results; no wrapping arithmetic.
  facts::Result<uint64_t> integer(mlir::Value, facts::Work &,
                                  unsigned depth = 0);
  facts::Status equalExtent(mlir::Value left, unsigned leftAxis,
                            mlir::Value right, unsigned rightAxis,
                            facts::Work &, unsigned depth = 0);
  facts::Status bound(mlir::Value index, mlir::Value container, unsigned axis,
                      facts::Work &, unsigned depth = 0);
  facts::Result<uint64_t> extent(mlir::Value, unsigned axis, facts::Work &,
                                 unsigned depth = 0);
  /// Upper bounds are not exact extents and never establish strict bounds.
  facts::Result<facts::Cardinality>
  cardinality(mlir::Value, unsigned axis, facts::Work &, unsigned depth = 0);

private:
  struct Impl;
  std::unique_ptr<Impl> impl_;
};
} // namespace zkc
#endif
