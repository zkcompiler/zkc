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
  // AfterFinalDraw requires that no participant makes a random-service query
  // after its own logical oracle query on a reached continuation. This includes
  // every service method and is checked against the frozen prepared source.
  // Neither this property nor Immediate authorizes batching or delayed proofs.
  OracleQueryFlush flush = OracleQueryFlush::Immediate;
};
} // namespace zkc::protocol
#endif
