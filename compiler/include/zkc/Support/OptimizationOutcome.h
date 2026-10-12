#ifndef ZKC_SUPPORT_OPTIMIZATIONOUTCOME_H
#define ZKC_SUPPORT_OPTIMIZATIONOUTCOME_H

#include <cstdint>
#include <optional>

namespace zkc {
/// Optional producer observations, never admission or verification evidence.
enum class OptimizationStatus {
  Succeeded,
  Unsupported,
  MissingEvidence,
  Capacity,
  PolicyDisabled,
  ReplacementRestricted,
  MissingRecipe
};
enum class OptimizationReason {
  None,
  Structure,
  Equation,
  EqualExtent,
  StrictBound,
  Depth,
  Cycle,
  Replacement,
  Recipe,
  Policy,
  OrderedRetry,
  LaneFormula,
  Work,
  CallEligibility,
  ImplementationRestriction
};
enum class WorkOwner {
  Structural,
  Equations,
  Evidence,
  Lanes,
  OptionalComparison,
  RequiredFiniteReader,
  HelperOperations,
  HelperSlots,
  Polynomial,
  FiniteExpressions,
  AlgorithmExpansion,
  AlgorithmOriginBytes,
  AlgorithmChecking
};
struct CapacityCause {
  WorkOwner owner;
  /// Absent for limits whose reader does not expose a failed debit.
  std::optional<uint64_t> requested = {}, available = {};
};
struct OptimizationOutcome {
  OptimizationStatus status = OptimizationStatus::Unsupported;
  OptimizationReason reason = OptimizationReason::Structure;
  std::optional<CapacityCause> capacity = {};
  /// Query operands are signature input positions; axes retain their meaning.
  std::optional<unsigned> input = {}, otherInput = {}, axis = {},
                          otherAxis = {};

  static OptimizationOutcome success() {
    return {OptimizationStatus::Succeeded, OptimizationReason::None};
  }
  static OptimizationOutcome exhausted(WorkOwner owner,
                                       std::optional<uint64_t> requested = {},
                                       std::optional<uint64_t> available = {}) {
    return {OptimizationStatus::Capacity, OptimizationReason::Work,
            CapacityCause{owner, requested, available}};
  }
};
} // namespace zkc
#endif
