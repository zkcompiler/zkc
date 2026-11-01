#ifndef ZKC_DIALECT_RUNTIME_PARAMETERS_H
#define ZKC_DIALECT_RUNTIME_PARAMETERS_H
#include "zkc/Contracts/NativeOrigin.h"
#include "zkc/Contracts/Numerical.h"
#include "zkc/Dialect/Runtime/IR/RuntimeAttrs.h"
namespace zkc::runtime {
/// Typed physical numerical data. Formation has no operand mask; invocation
/// admission independently checks the schedule under its binding's exact mask.
llvm::Expected<NumericalPlanAttr>
importNumericalPlan(mlir::MLIRContext *, const protocol::NumericalPlan &);
llvm::Expected<protocol::NumericalPlan> exportNumericalPlan(NumericalPlanAttr);
/// Explicit neutral-origin interchange. Native consumers read the attributes.
/// Formation checks source syntax and size, not source correspondence, setup
/// authority, transcript injectivity or cryptographic binding.
llvm::Expected<NativeOriginAttr>
importNativeOrigin(mlir::MLIRContext *, const protocol::NativeOriginTemplate &);
llvm::Expected<protocol::NativeOriginTemplate>
    exportNativeOrigin(NativeOriginAttr);
llvm::Expected<AssetReferenceAttr> decodeAssetReference(mlir::MLIRContext *,
                                                        llvm::StringRef format,
                                                        llvm::StringRef digest);
llvm::Expected<std::string> encodeAssetDigest(AssetReferenceAttr);
} // namespace zkc::runtime
#endif
