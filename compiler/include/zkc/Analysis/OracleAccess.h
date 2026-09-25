#ifndef ZKC_ANALYSIS_ORACLEACCESS_H
#define ZKC_ANALYSIS_ORACLEACCESS_H

#include "zkc/Source/Execution.h"
#include "llvm/Support/JSON.h"
#include <optional>

namespace zkc {

/// Logical operands of one actual authentication check. All strings naming
/// values refer to occurrences in the admitted source execution, including
/// distinct received values. No equality with the peer's value is inferred.
struct OracleAccess {
  std::string path, role, root, width, height, coordinate, row, proof, accepted;
  source::Names guards, coordinateDraws, coordinateReceptions;
  /// Received inputs absorbed by a sampling provider, distinct from inputs
  /// directly selecting the coordinate. This does not establish independence.
  source::Names coordinateProviderHistory, coordinateUnknowns;
  /// Exact local sample identity, not merely may-dependence on randomness.
  std::optional<std::string> coordinateSample;
  bool sampleBoundMatchesHeight = false;
  /// Transcript draw occurrences whose actual provider chain contains an
  /// observation at the checking role of this exact root value. The optional
  /// publication policy separately requires a received root/publication link.
  source::Names publicationBoundDraws;
  /// Optional linkage to the authored honest opening/commitment. This is
  /// program provenance, never a premise constraining malicious peer values.
  std::optional<std::string> opening, publication;
  std::optional<std::string> rootReception;
  bool openingCoordinateLinked = false;
  size_t ordinal = 0;
};

struct OracleFinding {
  std::string code, path;
};

struct OracleAccessReport {
  std::vector<OracleAccess> accesses;
  std::vector<OracleFinding> findings;
  std::optional<unsigned> acceptanceResult;
  std::optional<std::string> acceptanceRole;
};

struct OraclePolicy {
  /// Check publication order for contributing fresh query draws and exact root
  /// absorption for contributing transcript draws; refuse coordinates
  /// directly selected by received values. Absorbed transcript history is
  /// retained separately and does not establish a construction/security law.
  /// Constants and locally derived coordinates need not be exact samples.
  bool publicationBeforeQueries = false;
  /// Require every bounded index draw to precede every opening response.
  /// This is a construction policy, not a universal vector-commitment law.
  bool queriesBeforeResponses = false;
  /// An explicit caller contract: acceptance requires this entry Boolean
  /// result to be true. Zero-based index across ALL entry result ports,
  /// including other roles (unlike a construction descriptor's validator-only
  /// index). Ordinary returned Booleans are not acceptance sinks.
  std::optional<unsigned> acceptanceResult{};
  /// Require each checked coordinate to be an exact bounded-index sample and
  /// its bound to be the same local value as the check's height. This supplies
  /// neither publication ordering nor a sampler distribution/uniformity claim.
  bool sampledQueries = false;
};

/// Dataflow analysis over an already admitted, finite expanded execution.
/// Reports missing guard/linkage/order evidence instead of inventing it.
/// Defensive structural checks do not replace source admission. workLimit
/// bounds operation/operand visits, copied provenance elements and chain steps
/// across both passes; exhaustion reports oracle-analysis-limit and stops.
OracleAccessReport analyzeOracleAccess(const source::Execution &,
                                       OraclePolicy = {},
                                       size_t workLimit = 1000000);

/// Public entry point: admission and instantiation precede analysis.
llvm::Expected<OracleAccessReport> inspectOracleAccess(const source::Module &,
                                                       llvm::StringRef entry,
                                                       OraclePolicy = {});

llvm::json::Value encodeOracleAccess(const OracleAccessReport &);

} // namespace zkc
#endif
