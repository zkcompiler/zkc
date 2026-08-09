//===- SealedGuard.h - Action guard for sealed protocols --------*- C++ -*-===//
#ifndef ZKC_ARTIFACT_SEALEDGUARD_H
#define ZKC_ARTIFACT_SEALEDGUARD_H

#include "mlir/IR/MLIRContext.h"

namespace zkc {

/// Installs the sealing enforcement guard on `context`
/// (docs/spec/carrier.md §3): action-dispatched pattern applications
/// rooted under a `pir.sealed` are refused (with an audit remark);
/// everything else runs. The honest contract: pattern-level
/// interception is precise, but direct C++ mutation is not
/// action-wrapped — storage-level immutability of written artifacts
/// stays the primary enforcement, this guard is the second layer.
void installSealedGuard(mlir::MLIRContext &context);

} // namespace zkc

#endif // ZKC_ARTIFACT_SEALEDGUARD_H
