#ifndef ZKC_COMPILER_ORACLESCHEDULE_H
#define ZKC_COMPILER_ORACLESCHEDULE_H
#include <array>
#include <cstdint>

namespace zkc::protocol {
/// Abstract observation language for selecting the oracle opening policy.
/// Tracks whether a challenge draw can follow a query along one reached path,
/// keeping normal continuation separate from termination. It says nothing
/// about query batching, position totality, authentication or availability.
class OracleObservationSummary {
public:
  /// Empty/total work: preserves the incoming observation state.
  OracleObservationSummary();
  static OracleObservationSummary query();
  static OracleObservationSummary draw();
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
} // namespace zkc::protocol
#endif
