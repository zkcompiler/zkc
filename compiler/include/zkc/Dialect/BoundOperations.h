#ifndef ZKC_DIALECT_BOUNDOPERATIONS_H
#define ZKC_DIALECT_BOUNDOPERATIONS_H
#include "mlir/IR/Types.h"
#include "mlir/Support/LogicalResult.h"
namespace mlir {
class Operation;
}
namespace zkc::detail {
bool isLogicalOperationData(mlir::Type type);
mlir::LogicalResult verifyLogicalOperation(mlir::Operation *operation);
} // namespace zkc::detail
#endif
