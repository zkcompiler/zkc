#ifndef ZKC_PROTOCOL_ORACLEANALYSIS_H
#define ZKC_PROTOCOL_ORACLEANALYSIS_H
#include "mlir/IR/Value.h"
#include "llvm/ADT/StringRef.h"
namespace zkc::mathematical {
// Every possible dynamic anchor must have this holder. This bounded backward
// closure includes zero-trip values and future loop backedges. Availability is
// a separate check: knowing an anchor's holder does not recover a hidden role.
mlir::LogicalResult verifyOracleHolder(mlir::Value handle, llvm::StringRef role,
                                       mlir::Operation *use,
                                       unsigned &remaining);
} // namespace zkc::mathematical
#endif
