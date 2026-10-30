#ifndef ZKC_DIALECT_VERIFICATION_H
#define ZKC_DIALECT_VERIFICATION_H

#include "mlir/Support/LogicalResult.h"
namespace mlir {
class Operation;
}
namespace zkc {
// Internal stage-admission hook. Ordinary MLIR verification must have checked
// local invariants and nested operations first. Public callers use admitStage.
namespace protocol {
/// Whole executable protocol admission over native types, SSA and symbols.
/// Neither this nor MLIR verification establishes source-relative correctness.
mlir::LogicalResult verifyModule(mlir::Operation *root);
} // namespace protocol
} // namespace zkc
#endif
