#ifndef ZKC_TRANSFORMS_ORACLESCHEDULE_H
#define ZKC_TRANSFORMS_ORACLESCHEDULE_H
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include <array>
#include <cstdint>

namespace mlir {
class ModuleOp;
}
namespace zkc::protocol {
/// Abstract observation language for selecting the oracle opening policy.
/// Tracks whether a random-service query can follow an oracle query on one
/// path, keeping normal continuation separate from termination. It says nothing
/// about query batching, position totality, authentication or availability.
class OracleObservationSummary {
public:
  /// Empty/total work: preserves the incoming observation state.
  OracleObservationSummary();
  static OracleObservationSummary query();
  static OracleObservationSummary draw();
  /// Terminates this observation flow. A helper return or another participant's
  /// completion is not a stop of the flow being summarized.
  static OracleObservationSummary stop();
  /// Choice joins the possible paths, without inventing a cross-arm path.
  OracleObservationSummary either(const OracleObservationSummary &) const;
  /// Sequential composition continues only paths that return normally.
  OracleObservationSummary then(const OracleObservationSummary &) const;
  /// Exactly count iterations; stopped paths do not reach a later iteration.
  OracleObservationSummary repeat(uint64_t count) const;
  /// Any count from zero through maximum, inclusive. A source analysis must
  /// separately justify the bound and whether all these counts are possible.
  OracleObservationSummary repeatAtMost(uint64_t maximum) const;
  bool queryBeforeDraw() const;

private:
  // States: 0 = no query, 1 = query observed, 2 = later draw observed.
  // Each bit set records a possible exit state for one incoming state.
  using Relation = std::array<uint8_t, 3>;
  Relation normal, stopped;
  OracleObservationSummary(Relation normal, Relation stopped)
      : normal(normal), stopped(stopped) {}
};
/// Summarize one observer of an admitted, prepared protocol. Applications must
/// already be expanded. Constants are read from actual SSA; uncertain counts
/// use their checked maximum. Fallible local work may stop or continue, while
/// another participant's completion does not terminate this observer. This is
/// a conservative scheduling check, not authentication or a simulation proof.
llvm::Expected<OracleObservationSummary>
analyzeOracleObservations(mlir::ModuleOp prepared, llvm::StringRef entry,
                          llvm::StringRef observer);
/// Check every logical query owner in every prepared common entry. The policy
/// is participant-relative and includes every random-service method, not just
/// a designated public-coin service. One shared traversal budget covers all
/// entries and observers. It authorizes no batching or deferred authentication.
llvm::Error checkOracleFinalDrawSchedule(mlir::ModuleOp prepared);
} // namespace zkc::protocol
#endif
