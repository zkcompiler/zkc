#ifndef ZKC_DIALECT_ADMISSION_H
#define ZKC_DIALECT_ADMISSION_H

#include "mlir/Support/LogicalResult.h"

namespace mlir {
class Operation;
}
namespace zkc {
/// Read-only admission of a builtin module or protocol symbol-table owner.
/// Runs ordinary MLIR verification before checking each complete protocol
/// stage, including dormant declarations. Profile attributes describe intent;
/// they are never admission certificates. The caller must keep the inspected
/// owner and all of its nested IR stable for this call. Every call reads fresh
/// facts; mutation requires a new call before optimization or publication.
/// This does not establish correspondence to an earlier source or program.
mlir::LogicalResult admitStage(mlir::Operation *owner);
} // namespace zkc
#endif
