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
/// Admit one operation's executable closure and native deployment identities.
/// The caller supplies the independently selected source identity and role.
llvm::Error checkCpuOperationArtifact(llvm::StringRef bytes,
                                      llvm::StringRef original,
                                      llvm::StringRef role);
} // namespace zkc::detail
#endif
