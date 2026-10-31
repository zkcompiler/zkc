#ifndef ZKC_TRANSFORMS_ORACLEQUERYBLOCKS_H
#define ZKC_TRANSFORMS_ORACLEQUERYBLOCKS_H
#include "OracleQueryCapacity.h"
#include "mlir/IR/Dominance.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Transforms/OracleSelection.h"
#include <vector>
namespace zkc::protocol {
// One contiguous nonadaptive source window. This borrows the admitted source;
// it establishes neither query domains nor transport compatibility. Discovery
// preserves a valid demand prefix and defers a later domain cut to replay.
// The caller binds the selected source roots, exact controller family and
// actual packet/replay calls in its complete realization check.
struct OracleQueryWindowSelection {
  std::vector<protocol_ir::OracleQueryOp> queries;
  uint64_t leaves = 0;
};
llvm::Expected<OracleQueryWindowSelection>
selectOracleQueryWindow(protocol_ir::OracleQueryOp first, OracleAuthentication,
                        const OracleQueryCapacity &, mlir::DominanceInfo &,
                        unsigned &remaining);

} // namespace zkc::protocol
#endif
