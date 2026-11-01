#ifndef ZKC_TARGET_NUMERICALPLAN_H
#define ZKC_TARGET_NUMERICALPLAN_H
#include "zkc/Dialect/Runtime/Parameters.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
namespace zkc::target {
inline constexpr uint64_t NumericalConstructionWork = 64 * 1024 * 1024;
inline constexpr uint64_t NumericalCheckingWork = 16 * 1024 * 1024;
/// Transaction-local proposal reuse. Keys and values are immutable
/// context-owned attributes, never operations from a discarded candidate. A
/// cache hit is not evidence: the physical reader still checks every actual
/// selected occurrence.
class NumericalPlanProposals {
  uint64_t &remaining;
  llvm::DenseMap<mlir::ArrayAttr, runtime::NumericalPlanAttr> proposals;

public:
  explicit NumericalPlanProposals(uint64_t &remaining) : remaining(remaining) {}
  llvm::Expected<runtime::NumericalPlanAttr>
  propose(algebra::FieldType, algebra::RingExpressionAttr,
          mlir::DenseBoolArrayAttr,
          unsigned lanes = protocol::NumericalLimits::lanes);
};
/// Independent per-validation reuse of exact immutable source/candidate pairs.
/// This state is never shared with the producer or retained across IR changes.
class NumericalPlanChecks {
  uint64_t remaining = NumericalCheckingWork;
  llvm::DenseSet<mlir::ArrayAttr> accepted;

public:
  llvm::Error check(algebra::FieldType, algebra::RingExpressionAttr,
                    mlir::DenseBoolArrayAttr, runtime::NumericalPlanAttr);
};
/// CPU-owned proposal. Prime-field pointwise candidates pass the word and
/// private-tile readers; other complete domains select an opaque provider.
llvm::Expected<runtime::NumericalPlanAttr>
proposeNumericalPlan(algebra::FieldType, algebra::RingExpressionAttr,
                     mlir::DenseBoolArrayAttr,
                     unsigned lanes = protocol::NumericalLimits::lanes);
/// Independently read the actual plan and its relation to the logical subject.
/// Never replay target lowering, vectorization, or allocation to approve it.
llvm::Error verifyNumericalPlan(algebra::FieldType, algebra::RingExpressionAttr,
                                mlir::DenseBoolArrayAttr,
                                runtime::NumericalPlanAttr,
                                uint64_t *remaining = nullptr);
} // namespace zkc::target
#endif
