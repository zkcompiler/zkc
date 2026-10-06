#ifndef ZKC_LIB_COMPILER_NATIVE_PROOF_VERIFICATION_H
#define ZKC_LIB_COMPILER_NATIVE_PROOF_VERIFICATION_H
#include "zkc/Compiler/NativeProof.h"
namespace zkc::detail {
/// Source-admitted occurrence facts. The checker reads actual helper bodies;
/// generated helper names are not evidence of their meaning.
struct NativeTranscriptEvent {
  std::string site, origin;
  mlir::Type payload;
  bool query;
  unsigned depth = 0;
};
llvm::Error verifyNativeEntrySelection(mlir::ModuleOp prepared,
                                       mlir::ModuleOp selected,
                                       llvm::StringRef entry);
llvm::Error
verifyNativeTranscript(mlir::ModuleOp projected, mlir::ModuleOp constructed,
                       const NativeProofPolicy &policy,
                       llvm::ArrayRef<NativeTranscriptEvent> events);
} // namespace zkc::detail
#endif
