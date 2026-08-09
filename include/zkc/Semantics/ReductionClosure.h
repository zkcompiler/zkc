//===- ReductionClosure.h - exact local reduction judgment ------*- C++ -*-===//
#ifndef ZKC_SEMANTICS_REDUCTIONCLOSURE_H
#define ZKC_SEMANTICS_REDUCTIONCLOSURE_H

#include "mlir/Support/LogicalResult.h"

namespace mlir {
class Operation;
}

namespace zkc::registry {
class ProtocolVocabulary;
}

namespace zkc::semantics {
struct ClosureLedger;

/// Establish ReductionClosureOK for every reduction in one protocol container.
/// The caller owns `ledger` and passes it to terminal closure so material and
/// check use can be accounted across both independent producer judgments.
mlir::LogicalResult
verifyReductionClosure(mlir::Operation *container,
                       const registry::ProtocolVocabulary &vocabulary,
                       ClosureLedger &ledger);

} // namespace zkc::semantics

#endif // ZKC_SEMANTICS_REDUCTIONCLOSURE_H
