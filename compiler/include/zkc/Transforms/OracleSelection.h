#ifndef ZKC_TRANSFORMS_ORACLE_SELECTION_H
#define ZKC_TRANSFORMS_ORACLE_SELECTION_H
#include <optional>
#include <string>
#include <vector>
namespace zkc::protocol {
enum class OracleLeafGrouping { Individual, AntipodalPairs };
enum class OracleLeafOrder { Natural, BitReversed };
enum class OracleQueryFlush { Immediate, AfterFinalDraw };
struct OracleTableRealization {
  // Empty scheme selects ideal tables. Its layout must be the canonical
  // individual/natural choice; Merkle layout has no meaning on ideal data.
  std::string scheme;
  OracleLeafGrouping grouping = OracleLeafGrouping::Individual;
  OracleLeafOrder order = OracleLeafOrder::Natural;
  bool operator==(const OracleTableRealization &other) const {
    return scheme == other.scheme && grouping == other.grouping &&
           order == other.order;
  }
};
struct OracleRootSelection {
  std::string entry;
  std::vector<unsigned> path;
  OracleTableRealization realization;
};
struct OracleRealizationPolicy {
  // Absence explicitly requests ideal realization for every root. A present
  // inventory must cover every actual input/send occurrence exactly once;
  // unknown, duplicated or uncovered selectors never fall back to ideal.
  std::optional<std::vector<OracleRootSelection>> roots;
  // Post-final-draw needs the observation reader; query-bearing modules
  // currently refuse that choice rather than publishing an unchecked schedule.
  OracleQueryFlush flush = OracleQueryFlush::Immediate;
};
} // namespace zkc::protocol
#endif
