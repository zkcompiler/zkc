#ifndef ZKC_TRANSFORMS_ORACLETABLEREAD_H
#define ZKC_TRANSFORMS_ORACLETABLEREAD_H
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolTypes.h"
#include "llvm/Support/Error.h"
namespace zkc::protocol {
// Internal ideal-table primitive. Its arguments are data, actual rows and query
// position. The caller must bind data/rows to the source anchor at
// construction. Check the query domain before reading, even if the native
// vector is longer. This does not authenticate Merkle openings or discharge
// shape obligations.
llvm::Expected<mlir::func::FuncOp>
emitOracleTableRead(mlir::ModuleOp candidate, protocol_ir::OracleKindAttr kind);
// Read actual resolved bindings and outcome edges; no producer replay. This is
// a primitive check, not complete protocol-realization correspondence.
llvm::Error checkOracleTableRead(mlir::ModuleOp candidate,
                                 mlir::func::FuncOp actual,
                                 protocol_ir::OracleKindAttr kind);
} // namespace zkc::protocol
#endif
