#ifndef ZKC_DIALECT_VERIFICATION_H
#define ZKC_DIALECT_VERIFICATION_H

#include "mlir/Support/LogicalResult.h"
namespace mlir {
class Operation;
}
namespace zkc {
// Internal region-verifier hooks. MLIR must have verified local invariants and
// nested operations first. Public callers use mlir::verify or checked export.
namespace protocol {
/// Whole executable protocol admission over native types, SSA and symbols.
/// Neither this nor MLIR verification establishes source-relative correctness.
mlir::LogicalResult verifyModule(mlir::Operation *root);
} // namespace protocol
} // namespace zkc
#endif
