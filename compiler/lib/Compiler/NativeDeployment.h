#ifndef ZKC_LIB_COMPILER_NATIVE_DEPLOYMENT_H
#define ZKC_LIB_COMPILER_NATIVE_DEPLOYMENT_H
#include "zkc/Compiler/NativeProof.h"
namespace zkc::detail {
/// Decode the supplied outer bytes and compare retained policy/descriptor,
/// source port coordinates and the checked physical executable view. JSON
/// whitespace and equivalent string escapes do not change correspondence.
llvm::Error verifyNativeDeployment(
    mlir::ModuleOp source, mlir::ModuleOp physical, llvm::StringRef sourceBytes,
    const NativeProofPolicy &policy, const NativeProofOptions &options,
    const llvm::json::Value &descriptor, const llvm::json::Array &wireSites,
    llvm::StringRef bytes);
} // namespace zkc::detail
#endif
