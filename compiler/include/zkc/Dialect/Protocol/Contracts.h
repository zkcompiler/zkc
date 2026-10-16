#ifndef ZKC_DIALECT_PROTOCOL_CONTRACTS_H
#define ZKC_DIALECT_PROTOCOL_CONTRACTS_H

#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"

namespace zkc::protocol_ir {
// Declaration metadata only. The owner is the enclosing protocol definition.
// The native layout is documented in docs/spec/ir/protocols.md.
mlir::LogicalResult verifyContracts(MathematicalOp owner,
                                    mlir::SymbolTableCollection &symbols);
// Resolve an explicit selection in its containing protocol. Returns null for
// absent or unresolved selections; verifyContracts establishes full formation.
mlir::ArrayAttr getStatementTarget(StatementOp statement);
} // namespace zkc::protocol_ir

#endif
