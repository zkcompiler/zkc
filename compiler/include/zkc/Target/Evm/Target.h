#ifndef ZKC_TARGET_EVM_TARGET_H
#define ZKC_TARGET_EVM_TARGET_H

#include "zkc/Compiler/Evm.h"
#include "zkc/Transforms/EndpointClosure.h"
namespace zkc::evm {
/// The selected verifier endpoint as the exporter emits it. It is built once
/// from already checked facts while the complete source and the candidate are
/// available: the participant's logical signature, the original ports the
/// projection record assigns to the validator, and the construction's checked
/// descriptor rows. The exporter borrows it; nothing reparses the original or
/// derives a codec again.
struct EvmEndpoint {
  struct PublicInput {
    /// The logical type of the public row's endpoint input.
    mlir::Type type;
    /// The exact logical-tree prefix of its invocation row (role, original
    /// port and nominal type), which the value bytes follow.
    std::string rowPrefix;
  };
  /// The public inputs, in descriptor row order.
  llvm::SmallVector<PublicInput> publicInputs;
  /// The original output ports the endpoint returns, in canonical order, and
  /// the logical type of each.
  llvm::SmallVector<uint64_t> outputs;
  llvm::SmallVector<mlir::Type> results;
  /// The position in `results` of the selected Boolean acceptance.
  unsigned acceptance = 0;
  /// Whether the endpoint carries the managed transcript capability.
  bool transcript = false;
  /// The exact logical-tree prefix of the ten-element invocation root: its
  /// eight static elements, which the public rows and the context follow.
  std::string rootPrefix;
};
/// Build the endpoint from its checked facts: the participant's logical
/// signature, the validator's original input and output ports, the checked
/// descriptor and policy, and the SHA-256 of the exact original bytes.
llvm::Expected<EvmEndpoint> describeEndpoint(
    mlir::FunctionType logical, llvm::ArrayRef<uint64_t> inputPorts,
    llvm::ArrayRef<uint64_t> outputPorts, const llvm::json::Value &descriptor,
    const NativeProofPolicy &, llvm::StringRef originalSha256);
/// Read those facts from the selected participant and the complete source's
/// checked projection record.
llvm::Expected<EvmEndpoint>
describeEndpoint(const CheckedEndpoint &, const llvm::json::Value &descriptor,
                 const NativeProofPolicy &, llvm::StringRef originalSha256);
/// Lower only the independently checked selected executable closure. The
/// returned module borrows the endpoint's context. No source is mutated.
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>>
lowerEndpoint(const CheckedEndpoint &, const EvmOptions &);
/// Positive operation/type/effect legality, dominance and symbol verification.
mlir::LogicalResult checkTarget(mlir::ModuleOp);
/// Emit the actual legalized operations. The endpoint supplies the invocation
/// binding and the public and output schemas.
llvm::Expected<std::string> exportYul(mlir::ModuleOp, const EvmEndpoint &,
                                      const NativeProofPolicy &,
                                      const EvmLimits &);
} // namespace zkc::evm
#endif
