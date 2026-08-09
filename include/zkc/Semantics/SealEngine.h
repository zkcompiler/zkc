//===- SealEngine.h - one protocol seal implementation ---------*- C++ -*-===//
#ifndef ZKC_SEMANTICS_SEALENGINE_H
#define ZKC_SEMANTICS_SEALENGINE_H

#include "mlir/Support/LogicalResult.h"
#include "zkc/Dialect/Pir/PirOps.h"
#include "zkc/Registry/ProtocolEnvironment.h"

#include <utility>

namespace zkc::semantics {

/// The single implementation of protocol minting and registry-backed recheck.
/// Passes and in-memory compiler transforms are adapters over this class.
class SealEngine {
public:
  explicit SealEngine(registry::ProtocolEnvironment environment)
      : environment_(std::move(environment)) {}

  /// Judge and replace one open protocol. The source remains intact on every
  /// failure; success returns the newly minted sealed operation.
  mlir::FailureOr<pir::SealedOp> seal(pir::ProtocolOp protocol) const;

  /// Re-judge route semantics, the exact cited authority closure, and identity
  /// of an existing sealed artifact without mutating it.
  mlir::LogicalResult recheck(pir::SealedOp sealed) const;

private:
  registry::ProtocolEnvironment environment_;
};

} // namespace zkc::semantics

#endif // ZKC_SEMANTICS_SEALENGINE_H
