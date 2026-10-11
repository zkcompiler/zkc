#ifndef ZKC_ANALYSIS_COMPUTATIONWORK_H
#define ZKC_ANALYSIS_COMPUTATIONWORK_H

#include <cstdint>

namespace zkc::finite {
/// Optional recognition work shared across subjects and nested occurrences.
/// Evidence bounds extent/bound queries only; independent candidate checking
/// and required ordered realization retain their own allowances. Exhaustion
/// declines an optional fact or equation, never admission or ordered fallback.
struct ComputationWork {
  uint64_t structural = 100000;
  uint64_t equations = 100000;
  uint64_t evidence = 100000;
};

inline bool consumeComputationWork(uint64_t &remaining, uint64_t amount = 1) {
  if (remaining < amount) {
    remaining = 0;
    return false;
  }
  remaining -= amount;
  return true;
}
} // namespace zkc::finite
#endif
