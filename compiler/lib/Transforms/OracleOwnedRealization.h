#ifndef ZKC_TRANSFORMS_ORACLEOWNEDREALIZATION_H
#define ZKC_TRANSFORMS_ORACLEOWNEDREALIZATION_H

#include "OracleCommonPlan.h"
#include "OracleNativeCommon.h"

namespace zkc::mathematical {
class RealizedProtocol;
}
namespace zkc::protocol {
// Local create/check/publish boundary. No mutable handles or supplied evidence
// enter after creation. Only the complete independent checker constructs the
// retained analyses. The exact owners and allowance outlive these preflights;
// none of the preflights survives transfer into the persistent realized owner.
class OracleOwnedRealization {
  friend class mathematical::RealizedProtocol;
  friend llvm::Expected<OracleCommonRealization>
  emitOracleRealizationWithWork(mlir::ModuleOp, const OracleRealizationPolicy &,
                                OracleNativeWork &);
  OracleCommonRealization actual;
  OracleRealizationFacts facts;
  std::vector<OracleCommonAnalysis> analyses;
  OracleRealizationPolicy policy;
  std::vector<OracleRootSelection> selections;
  OracleNativeSourcePreflight sourcePreflight, candidatePreflight;
  OracleOwnedRealization(OracleCommonRealization actual,
                         OracleRealizationFacts facts,
                         std::vector<OracleCommonAnalysis> analyses,
                         OracleRealizationPolicy policy,
                         std::vector<OracleRootSelection> selections,
                         OracleNativeSourcePreflight sourcePreflight,
                         OracleNativeSourcePreflight candidatePreflight)
      : actual(std::move(actual)), facts(std::move(facts)),
        analyses(std::move(analyses)), policy(std::move(policy)),
        selections(std::move(selections)),
        sourcePreflight(std::move(sourcePreflight)),
        candidatePreflight(std::move(candidatePreflight)) {}
  static llvm::Expected<OracleOwnedRealization>
  create(mlir::ModuleOp, const OracleRealizationPolicy &, OracleNativeWork &);
  llvm::Expected<OracleRealizationPublication>
  publish(OracleNativeWork &) const;

public:
  OracleOwnedRealization(OracleOwnedRealization &&) = default;
  OracleOwnedRealization(const OracleOwnedRealization &) = delete;
};
} // namespace zkc::protocol
#endif
