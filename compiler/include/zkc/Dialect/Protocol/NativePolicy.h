#ifndef ZKC_DIALECT_PROTOCOL_NATIVEPOLICY_H
#define ZKC_DIALECT_PROTOCOL_NATIVEPOLICY_H
#include "zkc/Analysis/NativeTypes.h"
namespace zkc::mathematical {
mlir::LogicalResult verifyNativeExecution(mlir::Operation *unit);
mlir::LogicalResult verifyNativeExecution(mlir::Operation *unit,
                                          NativeTypePolicies &types);
mlir::LogicalResult verifyProjectionMetadata(mlir::Operation *unit,
                                             NativeTypePolicies &types);
} // namespace zkc::mathematical
#endif
