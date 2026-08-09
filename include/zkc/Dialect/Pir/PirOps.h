//===- PirOps.h - Protocol IR ops -------------------------------*- C++ -*-===//
#ifndef ZKC_DIALECT_PIR_PIROPS_H
#define ZKC_DIALECT_PIR_PIROPS_H

#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/OpImplementation.h"
#include "mlir/Interfaces/InferTypeOpInterface.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "zkc/Dialect/Pir/PirDialect.h"
#include "zkc/Dialect/Pir/PirInterfaces.h"
#include "zkc/Dialect/Pir/PirTypes.h"

namespace zkc {
namespace pir {

/// The side-effect resource every protocol op writes (carrier.md §3).
/// One resource covers all protocol content: CSE never merges protocol
/// ops, DCE never drops result-less ones (checks, sinks, end), and
/// motion passes stay conservative — without dialect-specific pass
/// hooks. Defense in depth on top of token threading; the chain-safety
/// regression is the empirical gate.
struct ProtocolResource
    : public mlir::SideEffects::Resource::Base<ProtocolResource> {
  llvm::StringRef getName() const final { return "pir.protocol"; }
};

} // namespace pir
} // namespace zkc

#include "zkc/Dialect/Pir/PirOpsEnums.h.inc"

#define GET_OP_CLASSES
#include "zkc/Dialect/Pir/PirOps.h.inc"

#endif // ZKC_DIALECT_PIR_PIROPS_H
