#ifndef ZKC_TRANSFORMS_ORACLEMERKLE_H
#define ZKC_TRANSFORMS_ORACLEMERKLE_H
#include "OracleLayout.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolTypes.h"
#include "llvm/Support/Error.h"
namespace zkc::protocol {
// Ordinary scoped helpers, with no new runtime kernel or semantic authority.
// Position: (rows, query) -> (physical height, leaf, payload slot).
// Commit: (logical data, rows) -> (root, private opening state).
// Open: (opening state, rows, query) -> (complete row, proof).
// Authenticate: (root, rows, query, complete row, proof) -> logical answer.
// Every helper checks the dynamic positive power-of-two shape and query domain.
// Authentication guards the complete row before selecting the payload slot.
// The enclosing realization must still bind roots, shape, state and exchanges
// to the actual source anchor; these checks alone are not that correspondence.
struct OracleMerkleFunctions {
  mlir::func::FuncOp position, commit, open, authenticate;
};
llvm::Expected<OracleMerkleFunctions>
emitOracleMerkle(mlir::ModuleOp candidate, protocol_ir::OracleKindAttr,
                 llvm::StringRef scheme, OracleLeafGrouping, OracleLeafOrder);
// Check actual resolved bodies and ordered outcome edges, without replaying
// the producer. Only direct field tables match the installed scheme signature.
llvm::Error checkOracleMerkle(mlir::ModuleOp candidate,
                              const OracleMerkleFunctions &,
                              protocol_ir::OracleKindAttr,
                              llvm::StringRef scheme, OracleLeafGrouping,
                              OracleLeafOrder);
} // namespace zkc::protocol
#endif
