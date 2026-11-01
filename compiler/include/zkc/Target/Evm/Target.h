#ifndef ZKC_TARGET_EVM_TARGET_H
#define ZKC_TARGET_EVM_TARGET_H

#include "zkc/Compiler/Evm.h"
#include "zkc/Transforms/EndpointClosure.h"
namespace zkc::evm {
/// Lower only the independently checked selected executable closure. The
/// returned module borrows the endpoint's context. No source is mutated.
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>>
lowerEndpoint(const CheckedEndpoint &, const EvmOptions &);
/// Positive operation/type/effect legality, dominance and symbol verification.
mlir::LogicalResult checkTarget(mlir::ModuleOp);
/// Emit the actual legalized operations. Descriptor/source are separately
/// checked construction metadata used only for invocation binding and schemas.
llvm::Expected<std::string> exportYul(mlir::ModuleOp,
                                      llvm::StringRef originalBytes,
                                      const llvm::json::Value &descriptor,
                                      const NativeProofPolicy &,
                                      const EvmLimits &);
} // namespace zkc::evm
#endif
