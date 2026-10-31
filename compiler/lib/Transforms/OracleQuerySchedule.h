#ifndef ZKC_TRANSFORMS_ORACLEQUERYSCHEDULE_H
#define ZKC_TRANSFORMS_ORACLEQUERYSCHEDULE_H
#include "OracleCommonPlan.h"
namespace zkc::protocol {
struct OracleRemoteRequirement {
  unsigned receiver, holder;
  OracleQueryExchange exchange;
};
struct OracleBatchRequirement {
  std::vector<std::vector<unsigned>> queries;
  std::vector<unsigned> remotes;
  uint64_t leaves = 0;
};
struct OracleQuerySchedule {
  uint64_t capacity = 1;
  std::vector<OracleRemoteRequirement> remotes;
  std::vector<OracleBatchRequirement> batches;
};
// Derive source occurrence order, nonadaptivity, complete role/constructor
// transport compatibility and finite capacity. Supplied controllers and Merkle
// models require independent actual-body checks before this recipe can be used
// to accept a candidate. This never emits or reads producer metadata.
llvm::Expected<OracleQuerySchedule> planOracleQuerySchedule(
    mlir::ModuleOp prepared, llvm::StringRef entry,
    const OracleCommonRequirements &,
    llvm::ArrayRef<OracleCommonController>,
    llvm::ArrayRef<OracleMerkleFunctions>, OracleAuthentication);
} // namespace zkc::protocol
#endif
