#ifndef ZKC_ANALYSIS_EXECUTION_OBSERVATIONS_H
#define ZKC_ANALYSIS_EXECUTION_OBSERVATIONS_H

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Pass/AnalysisManager.h"
#include "zkc/Contracts/MathematicalFacts.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/Support/Error.h"
#include <memory>

namespace zkc {
/// Conservative dependencies on data formals, excluding the borrowed scope.
/// Results describe returning paths only; stops are logical, not budget or
/// allocation failures. Empty sets never mean that an unsupported body passed.
struct ExecutionObservationSummary {
  llvm::SmallVector<llvm::BitVector> results;
  llvm::BitVector stops;
  bool mayReturn = false, mayStop = false;
  unsigned depth = 1;
  /// Direct actual associations. Repeated callers share the callee summary;
  /// primitive occurrences retain binding, parameters and implementation on IR.
  llvm::SmallVector<mlir::func::FuncOp> callees;
  llvm::SmallVector<mlir::Operation *> primitives;
};

/// Builtin-module analysis of an admitted immutable source closure. It reuses
/// the checked scoped execution reader and mathematical closure owner. It does
/// not establish transcript binding, totality or a cryptographic
/// interpretation. Only immutable data and declared deterministic partial
/// primitives are supported. Unknown effects refuse even in an unused or
/// zero-result call.
///
/// Clear BEFORE changing any inspected body, type, binding or symbol. Returned
/// pointers expire at clear/invalidation/destruction; the module outlives them.
/// Source and candidate snapshots need separate analyses. Construction and
/// cache queries debit caller Work; callers debit their own substitutions.
/// Exhaustion or a failed query is sticky until clear. This is not thread-safe.
class ExecutionObservationAnalysis {
public:
  explicit ExecutionObservationAnalysis(mlir::Operation *module);
  ExecutionObservationAnalysis(mlir::Operation *module,
                               mlir::AnalysisManager &);
  ~ExecutionObservationAnalysis();
  ExecutionObservationAnalysis(const ExecutionObservationAnalysis &) = delete;
  ExecutionObservationAnalysis &
  operator=(const ExecutionObservationAnalysis &) = delete;
  bool isInvalidated(const mlir::AnalysisManager::PreservedAnalyses &);
  void clear();
  mlir::Operation *getOwner() const;
  /// Refusals distinguish owner/unsupported semantics/capacity. Scope/data ABI,
  /// closed control and finite callbacks must already be admitted by the owner.
  llvm::Expected<const ExecutionObservationSummary *>
  get(mlir::func::FuncOp function, facts::Work &);

private:
  struct Impl;
  std::unique_ptr<Impl> impl_;
};
} // namespace zkc
#endif
