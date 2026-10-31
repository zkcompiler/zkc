#ifndef ZKC_LIB_COMPILER_NATIVE_PROOF_VERIFICATION_H
#define ZKC_LIB_COMPILER_NATIVE_PROOF_VERIFICATION_H
#include "NativeRequest.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Dialect/Protocol/Construction.h"
#include <cstdint>
#include <optional>
namespace zkc::detail {
/// Source-admitted occurrence facts. The checker reads actual helper bodies;
/// generated helper names are not evidence of their meaning.
struct NativeTranscriptEvent {
  std::string site, origin;
  mlir::Type payload;
  bool query;
  unsigned depth = 0;
  /// The static UniformIndex domain of an index query; absent for field draws
  /// and message observations.
  std::optional<uint64_t> bound;
  /// Present only for a child construction start, including an empty input
  /// list.
  std::optional<llvm::SmallVector<mlir::Type>> startInputs = std::nullopt;
  std::optional<uint64_t> count = std::nullopt;
  std::optional<unsigned> difficulty = std::nullopt;
  std::string witnessSite = {};
  /// Deterministic V-to-P transport admitted by the actual-body value relation;
  /// it remains an observation but does not consume a selected challenge.
  bool reconstructed = false;
};
llvm::Error verifyNativeEntrySelection(mlir::ModuleOp prepared,
                                       mlir::ModuleOp selected,
                                       llvm::StringRef entry);
llvm::Error verifyNativeTranscript(
    mlir::ModuleOp projected, mlir::ModuleOp constructed,
    const NativeProofPolicy &policy,
    llvm::ArrayRef<NativeTranscriptEvent> events,
    const protocol::ConstructionPlan *construction = nullptr,
    llvm::ArrayRef<protocol::ConstructionInvocation> invocations = {},
    const mathematical::RealizedProtocol *realization = nullptr);
} // namespace zkc::detail
#endif
