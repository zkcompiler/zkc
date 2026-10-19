#ifndef ZKC_DIALECT_PROTOCOL_NATIVEPOLICY_H
#define ZKC_DIALECT_PROTOCOL_NATIVEPOLICY_H
#include "zkc/Analysis/NativeTypes.h"
namespace zkc::mathematical {
/// Admit a closed logical Local fragment containing only functions and
/// bindings in an exec-profile Protocol owner. Checks MLIR child invariants,
/// native types and the existing local-definition grammar/resources. No
/// participant Entry is required; whole-program admission remains separate.
mlir::LogicalResult verifyLocalFragment(mlir::Operation *unit);
mlir::LogicalResult verifyNativeLocals(mlir::Operation *unit, bool allowApply,
                                       NativeTypePolicies &types);
mlir::LogicalResult verifyNativeLocals(mlir::Operation *unit, bool allowApply);
mlir::LogicalResult verifyNativeExecution(mlir::Operation *unit);
mlir::LogicalResult verifyNativeExecution(mlir::Operation *unit,
                                          NativeTypePolicies &types);
mlir::LogicalResult verifyProjectionMetadata(mlir::Operation *unit,
                                             NativeTypePolicies &types);
} // namespace zkc::mathematical
#endif
