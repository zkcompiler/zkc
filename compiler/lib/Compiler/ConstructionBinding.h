#ifndef ZKC_COMPILER_CONSTRUCTIONBINDING_H
#define ZKC_COMPILER_CONSTRUCTIONBINDING_H
#include "NativeProofVerification.h"
namespace zkc::detail {
/// Requires independently checked candidate/source transcript correspondence.
/// This adds actual canonical-encoding/state coverage, never execution
/// admission.
llvm::Expected<llvm::json::Value> analyzeConstructionBinding(
    mlir::ModuleOp candidate, llvm::ArrayRef<mlir::Type> sourceInputs,
    const NativeProofPolicy &, NativeProofBindingProfile,
    llvm::ArrayRef<NativeTranscriptEvent>, const protocol::ConstructionPlan *);
} // namespace zkc::detail
#endif
