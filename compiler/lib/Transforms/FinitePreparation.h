#ifndef ZKC_TRANSFORMS_FINITEPREPARATION_H
#define ZKC_TRANSFORMS_FINITEPREPARATION_H

#include "zkc/Analysis/ComputationWork.h"
#include "zkc/Analysis/Finite.h"
#include <optional>

namespace zkc::finite {
// Private optional policy, independent of all required construction reserves.
inline constexpr uint64_t callbackStructuralLimit = 8192;

// One envelope covers discovery, preparation and structural selection. The
// existing counter APIs spend the local view; every exit retains those debits,
// including failed attempts. Equation/evidence allowances remain cumulative.
class CallbackStructuralWork {
  ComputationWork &shared;
  OptimizationOutcome &outcome;
  uint64_t initial;
  bool limitedByCallback;

public:
  ComputationWork remaining;
  CallbackStructuralWork(ComputationWork &shared, OptimizationOutcome &outcome);
  ~CallbackStructuralWork();
  CallbackStructuralWork(const CallbackStructuralWork &) = delete;
  CallbackStructuralWork &operator=(const CallbackStructuralWork &) = delete;
};

// Read the admitted immutable helper DAG once per invocation. The result is
// normalization work (copying, the final scan, and the private context), capped
// at callbackStructuralLimit + 1. Sizing itself spends structural work; an
// estimate never debits hypothetical copies. No cache survives this invocation.
std::optional<uint64_t> sizeCallbackPreparation(const Computation &computation,
                                                mlir::Operation *root,
                                                uint64_t &structural,
                                                OptimizationOutcome &outcome);
} // namespace zkc::finite
#endif
