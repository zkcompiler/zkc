#ifndef ZKC_LIB_COMPILER_NATIVE_CODEC_H
#define ZKC_LIB_COMPILER_NATIVE_CODEC_H
#include "NativeProofVerification.h"
namespace zkc::detail {
/// Replace typed proof transport after transcript construction has been
/// checked. Codec bodies remain ordinary Local functions; slicing and exit
/// control are compiler-owned adapters. The separate correspondence checker
/// reads both.
llvm::Expected<llvm::json::Array>
constructNativeCodec(mlir::ModuleOp module, const NativeProofPolicy &policy,
                     const protocol::ConstructionPlan &plan,
                     llvm::ArrayRef<NativeTranscriptEvent> events,
                     const llvm::json::Array &transcript);
llvm::Error verifyNativeCodec(mlir::ModuleOp transcript, mlir::ModuleOp encoded,
                              const NativeProofPolicy &policy,
                              const protocol::ConstructionPlan &plan,
                              llvm::ArrayRef<NativeTranscriptEvent> events,
                              const llvm::json::Array &transcriptPlan,
                              const llvm::json::Array &codecPlan);
} // namespace zkc::detail
#endif
