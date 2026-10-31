#ifndef ZKC_DIALECT_PROTOCOL_ORACLEPORTS_H
#define ZKC_DIALECT_PROTOCOL_ORACLEPORTS_H
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
namespace zkc::mathematical {
// Logical interface association only. Pairing does not assert equality between
// holder data and a receiver component or authenticate any commitment.
struct OraclePortPair {
  unsigned data, anchor;
  // The complete logical type retains both the family and sequence capacity.
  mlir::Type type;
  mlir::StringAttr holder;
  mlir::ArrayAttr receivers;
};
struct OraclePortLayout {
  llvm::SmallVector<OraclePortPair> inputs, outputs;
};
// Read pairs in anchor-port order using the same rules as interface admission.
// Results select the first unused matching holder-data leaf. Actual component
// views and retained applications determine pairing, not matching types alone.
// This checks the interface only, not whole-program or realization admission.
// Attributes borrow the source MLIRContext; mutation invalidates this layout.
mlir::FailureOr<OraclePortLayout>
readOraclePortLayout(protocol_ir::MathematicalOp, mlir::SymbolTableCollection &,
                     unsigned &remaining);
} // namespace zkc::mathematical
#endif
