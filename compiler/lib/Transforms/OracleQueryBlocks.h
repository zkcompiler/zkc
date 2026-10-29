#ifndef ZKC_TRANSFORMS_ORACLEQUERYBLOCKS_H
#define ZKC_TRANSFORMS_ORACLEQUERYBLOCKS_H
#include "OracleAnchorStorage.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Transforms/OracleSelection.h"
#include <optional>
namespace zkc::protocol {
// Source-derived evidence for crossing a base query's domain check. Borrows the
// admitted immutable prepared entry. An upper shape bound or a virtual law is
// never evidence that an actual position is valid.
struct OracleDirectQuery {
  protocol_ir::OracleQueryOp operation;
  unsigned constructor;
  mlir::Value anchor, position;
  uint64_t rows;
  std::optional<uint64_t> literal;
};
llvm::Expected<std::optional<OracleDirectQuery>>
admitOracleDirectQuery(protocol_ir::OracleQueryOp, const OracleAnchorStorage &,
                       unsigned &remaining);
// Sharing requires the same actual source reference, not a possible origin,
// equal root or equal data. The selected layout determines physical equality.
llvm::Expected<bool> shareOracleOpening(const OracleDirectQuery &,
                                        const OracleDirectQuery &,
                                        llvm::ArrayRef<OracleTableRealization>);
} // namespace zkc::protocol
#endif
