//===- OirOps.h - Operator-layer ops ----------------------------*- C++ -*-===//
#ifndef ZKC_DIALECT_OIR_OIROPS_H
#define ZKC_DIALECT_OIR_OIROPS_H

#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/OpImplementation.h"
#include "mlir/Interfaces/InferTypeOpInterface.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "zkc/Dialect/Oir/OirDialect.h"
#include "zkc/Dialect/Oir/OirTypes.h"

namespace zkc {
namespace oir {

/// The side-effect resource every endpoint protocol event writes
/// (docs/spec/endpoints.md §1): transcript, stream, binding, check, and
/// decision events are protected from merging, deletion, and motion;
/// pure algebra is the region where rewriting is legal again.
struct EndpointResource
    : public mlir::SideEffects::Resource::Base<EndpointResource> {
  llvm::StringRef getName() const final { return "oir.endpoint"; }
};

/// The closed endpoint-kind vocabulary (docs/spec/endpoints.md §5.1). One
/// spelling for every consumer — the artifact verifier, the encoder, the
/// interpreter, and projection all read these; `verifier_gadget` is
/// reserved and refused at the artifact verifier.
inline constexpr llvm::StringLiteral kEndpointVerifier{"verifier"};
inline constexpr llvm::StringLiteral kEndpointProverSkeleton{
    "prover_skeleton"};
inline constexpr llvm::StringLiteral kEndpointVerifierGadgetReserved{
    "verifier_gadget"};

} // namespace oir
} // namespace zkc

#define GET_OP_CLASSES
#include "zkc/Dialect/Oir/OirOps.h.inc"

#endif // ZKC_DIALECT_OIR_OIROPS_H
