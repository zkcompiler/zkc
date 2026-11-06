#ifndef ZKC_TRANSFORMS_ORACLECHECKEDREADER_H
#define ZKC_TRANSFORMS_ORACLECHECKEDREADER_H

#include "OracleCommonPlan.h"

namespace zkc::protocol {
class OracleVerificationContext;

// These facts are created only inside the complete paired reader, after the
// corresponding full primitive check. They borrow that invocation's const
// model and immutable contexts and never escape it. Raw primitive readers
// cannot manufacture them or use a mutable module as checking authority.
class OracleCheckedController {
  friend llvm::Error checkOracleRealizationModel(
      const OracleVerificationContext &, const OracleVerificationContext &,
      llvm::ArrayRef<OracleCommonEntryRealization>,
      llvm::ArrayRef<OracleRootSelection>, OracleAuthentication,
      OracleRealizationFacts *, OracleNativeWork *,
      const OracleNativeSourcePreflight *, const OracleNativeSourcePreflight *,
      std::vector<OracleCommonAnalysis> *);
  const OracleVerificationContext *target, *source;
  const OracleAnchorStorage *storage;
  const OracleQueryController *controller;
  OracleCheckedController(const OracleVerificationContext &target,
                          const OracleVerificationContext &source,
                          const OracleAnchorStorage &storage,
                          const OracleQueryController &controller)
      : target(&target), source(&source), storage(&storage),
        controller(&controller) {}

public:
  bool matches(const OracleVerificationContext &target,
               const OracleVerificationContext &source,
               const OracleAnchorStorage &storage,
               const OracleQueryController &controller) const {
    return this->target == &target && this->source == &source &&
           this->storage == &storage && this->controller == &controller;
  }
};
class OracleCheckedResponse {
  friend llvm::Error checkOracleRealizationModel(
      const OracleVerificationContext &, const OracleVerificationContext &,
      llvm::ArrayRef<OracleCommonEntryRealization>,
      llvm::ArrayRef<OracleRootSelection>, OracleAuthentication,
      OracleRealizationFacts *, OracleNativeWork *,
      const OracleNativeSourcePreflight *, const OracleNativeSourcePreflight *,
      std::vector<OracleCommonAnalysis> *);
  const OracleVerificationContext *context;
  const OracleQueryExchange *exchange;
  const OracleQueryResponse *response;
  OracleCheckedResponse(const OracleVerificationContext &context,
                        const OracleQueryExchange &exchange,
                        const OracleQueryResponse &response)
      : context(&context), exchange(&exchange), response(&response) {}

public:
  bool matches(const OracleVerificationContext &context,
               const OracleQueryExchange &exchange,
               const OracleQueryResponse &response) const {
    return this->context == &context && this->exchange == &exchange &&
           this->response == &response;
  }
};
} // namespace zkc::protocol
#endif
