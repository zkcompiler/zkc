#ifndef ZKC_TRANSFORMS_MATHEMATICALWORK_H
#define ZKC_TRANSFORMS_MATHEMATICALWORK_H

#include "zkc/Analysis/ComputationWork.h"
#include <cstdint>

namespace zkc::mathematical {
/// Compiler work for one mathematical realization stage. Share this object
/// across its definitions and nested expressions; it contains no IR evidence
/// and grants no admission. Optional lane exhaustion retains an ordered finite
/// path. Required helper/polynomial expansion must report a capacity refusal.
/// These counters are separate from runtime resource accounting.
struct RealizationWork {
  finite::ComputationWork matching;
  uint64_t lanes = 1000000;
  unsigned helperOperations = 100000;
  uint64_t helperSlots = 1000000;
  uint64_t polynomial = 100000;
  unsigned finiteExpressions = 100000;
};
} // namespace zkc::mathematical
#endif
