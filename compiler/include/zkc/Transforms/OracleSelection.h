#ifndef ZKC_TRANSFORMS_ORACLE_SELECTION_H
#define ZKC_TRANSFORMS_ORACLE_SELECTION_H
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"
#include <string>
#include <variant>
#include <vector>
namespace zkc::protocol {
enum class OracleLeafGrouping { Individual, AntipodalPairs };
enum class OracleLeafOrder { Natural, BitReversed };
enum class OracleQueryOrder { Unrestricted, AfterFinalDraw };
enum class OracleAuthentication { PerQuery, AtomicBlocks };
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
  bool operator==(const OracleRootSelection &other) const {
    return entry == other.entry && path == other.path &&
           realization == other.realization;
  }
};
struct OracleRealizationPolicy {
  // A uniform implementation or an exact inventory of actual base roots.
  // Unknown, duplicated or uncovered selectors never fall back to ideal.
  std::variant<OracleTableRealization, std::vector<OracleRootSelection>> roots =
      OracleTableRealization{};
  // AfterFinalDraw requires that no participant makes a random-service query
  // after its own logical oracle query on a reached continuation. This includes
  // every service method and is checked against the frozen prepared source.
  // Ordering alone authorizes neither batching nor delayed authentication.
  OracleQueryOrder order = OracleQueryOrder::Unrestricted;
  // Atomic windows require nonadaptive operands and preserve source barriers.
  // Answer-free discovery retains a valid prefix before a later domain cut;
  // all selected authentications precede replay and source-answer release.
  OracleAuthentication authentication = OracleAuthentication::PerQuery;
  bool operator==(const OracleRealizationPolicy &other) const {
    return roots == other.roots && order == other.order &&
           authentication == other.authentication;
  }
};
/// Strict bounded zkc.oracle-selection/0 request, independent of source
/// inventory.
llvm::Expected<OracleRealizationPolicy>
parseOracleRealizationPolicy(llvm::StringRef text);
/// Validate a typed request even when the prepared source has no base roots.
llvm::Error validateOracleRealizationPolicy(const OracleRealizationPolicy &);
/// Encode a valid request with exact selectors sorted by entry and path.
llvm::Expected<llvm::json::Value>
encodeOracleRealizationPolicy(const OracleRealizationPolicy &);

} // namespace zkc::protocol
#endif
