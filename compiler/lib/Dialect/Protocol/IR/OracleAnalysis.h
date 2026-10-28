#ifndef ZKC_PROTOCOL_ORACLEANALYSIS_H
#define ZKC_PROTOCOL_ORACLEANALYSIS_H
#include "mlir/IR/Value.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "llvm/ADT/StringRef.h"
namespace zkc::mathematical {
class TotalClosure;
class NativeTypePolicies;
// All retained query declarations share the common module's admission budget.
mlir::LogicalResult
verifyOracleDefinitions(protocol_ir::ProtocolModuleOp module,
                        TotalClosure &helpers, NativeTypePolicies &types,
                        unsigned &remaining);
// Every possible dynamic anchor must have this holder. This bounded backward
// closure includes zero-trip values and future loop backedges. Availability is
// a separate check: knowing an anchor's holder does not recover a hidden role.
mlir::LogicalResult verifyOracleHolder(mlir::Value handle, llvm::StringRef role,
                                       mlir::Operation *use,
                                       unsigned &remaining);
// Raw handle ports are paired with their holder data by actual SSA operands.
mlir::LogicalResult verifyOracleEntryPorts(protocol_ir::MathematicalOp program,
                                           unsigned &remaining);
mlir::LogicalResult
verifyOracleResultPorts(protocol_ir::MathematicalOp program,
                        mlir::SymbolTableCollection &symbols,
                        unsigned &remaining);
mlir::LogicalResult
verifyOracleApplicationPorts(protocol_ir::ApplyOp application,
                             mlir::SymbolTableCollection &symbols,
                             unsigned &remaining);
mlir::LogicalResult verifyOracleInputPair(protocol_ir::OracleInputOp input,
                                          mlir::SymbolTableCollection &symbols,
                                          unsigned &remaining);
// Check initially bound dimensions through actual applications, handle
// selection and loop backedges. One shared allowance bounds all substitutions.
mlir::LogicalResult
verifyInitialOracleShape(mlir::Value value, protocol_ir::MathematicalOp program,
                         mlir::Operation *use,
                         mlir::SymbolTableCollection &symbols,
                         unsigned &remaining);
} // namespace zkc::mathematical
#endif
