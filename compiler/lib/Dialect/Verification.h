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
/// Whole protocol check through IR reconstruction and executable admission.
/// Neither this nor MLIR verification establishes source-relative correctness.
mlir::LogicalResult verifyModule(mlir::Operation *root);
/// Admit all closed local definitions through the existing executable grammar.
mlir::LogicalResult verifyLocalDefinitions(mlir::Operation *root);
} // namespace protocol
} // namespace zkc
#endif
