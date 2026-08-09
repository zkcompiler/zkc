//===- TerminalClosure.h - static terminal attachment judgment -*- C++ -*-===//
#ifndef ZKC_SEMANTICS_TERMINALCLOSURE_H
#define ZKC_SEMANTICS_TERMINALCLOSURE_H

#include "mlir/Support/LogicalResult.h"

namespace mlir {
class Operation;
}

namespace zkc {
namespace registry {
class ProtocolVocabulary;
} // namespace registry

namespace semantics {

struct ClosureLedger;

/// Checks every profile, check contract, and discharge in one protocol
/// container, including the material-binding edges selected by terminal
/// attachments. Diagnostics are emitted on the responsible IR operation and
/// accumulate. This is a judgment, not a view-construction API;
/// consumers reconstruct their own derived views independently.
/// Material-use and producer-check ownership are shared with the reduction
/// judgment through `ledger`; whole-container unused-material accounting is a
/// caller responsibility after both judgments have run.
mlir::LogicalResult
verifyTerminalClosure(mlir::Operation *container,
                      const registry::ProtocolVocabulary &vocabulary,
                      ClosureLedger &ledger);

} // namespace semantics
} // namespace zkc

#endif // ZKC_SEMANTICS_TERMINALCLOSURE_H
