#ifndef ZKC_DIALECT_KERNEL_SUPPORT_H
#define ZKC_DIALECT_KERNEL_SUPPORT_H
#include "mlir/IR/Types.h"
#include "mlir/Support/LogicalResult.h"
namespace mlir {
class Operation;
}
namespace zkc::detail {
bool isLogicalKernelData(mlir::Type type);
mlir::LogicalResult verifyLogicalKernel(mlir::Operation *operation);
} // namespace zkc::detail
#endif
