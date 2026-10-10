#ifndef ZKC_TRANSFORMS_ALGORITHMSUPPORT_H
#define ZKC_TRANSFORMS_ALGORITHMSUPPORT_H
#include "zkc/Transforms/Algorithms.h"
#include <map>
#include <tuple>

namespace zkc::protocol::detail {
// One record per site, with both the logical definition and concrete local
// declaration retained. A call record describes its occurrence, not its callee.
struct AlgorithmOccurrence {
  std::string definition, declaration, originalSite;
  Assignments path;
  unsigned depth = 0;
  bool operator==(const AlgorithmOccurrence &other) const {
    return std::tie(definition, declaration, originalSite, path, depth) ==
           std::tie(other.definition, other.declaration, other.originalSite,
                    other.path, other.depth);
  }
};
using OccurrenceKey = std::pair<std::string, std::string>;
struct AlgorithmExpansionRecord {
  std::map<OccurrenceKey, AlgorithmOccurrence> occurrences;
  uint64_t work = 32768, originBytes = 16 * 1024 * 1024;
  uint64_t checkWork = 1000000, checkOriginBytes = 16 * 1024 * 1024;
  bool retained = false, finished = false;
};
struct AlgorithmStateAccess {
  static const AlgorithmExpansionRecord &get(const AlgorithmExpansionState &s) {
    static const AlgorithmExpansionRecord empty;
    return s.record ? *s.record : empty;
  }
  static void set(AlgorithmExpansionState &s, AlgorithmExpansionRecord value) {
    s.record =
        std::make_shared<const AlgorithmExpansionRecord>(std::move(value));
  }
};
inline const AlgorithmOccurrence *
occurrence(const AlgorithmExpansionRecord &record, llvm::StringRef function,
           llvm::StringRef site) {
  auto found = record.occurrences.find({function.str(), site.str()});
  return found == record.occurrences.end() ? nullptr : &found->second;
}
// Internal checker entry also returns independent remaining checker budgets.
mlir::LogicalResult
checkAlgorithmExpansion(mlir::ModuleOp before, mlir::ModuleOp after,
                        AlgorithmExpansionPhase phase,
                        const AlgorithmExpansionRecord &input,
                        AlgorithmExpansionRecord &output, bool compareRecords);
} // namespace zkc::protocol::detail
#endif
