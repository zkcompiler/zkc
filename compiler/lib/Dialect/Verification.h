#ifndef ZKC_DIALECT_VERIFICATION_H
#define ZKC_DIALECT_VERIFICATION_H

#include "mlir/Support/LogicalResult.h"
namespace mlir {
class Operation;
}
namespace zkc {
// Internal region-verifier hooks. MLIR must have verified local invariants and
// nested operations first. Public callers use mlir::verify or checked export.
/// Whole finite-table program check through its installed source library.
mlir::LogicalResult verifyProgram(mlir::Operation *program);
namespace protocol {
/// Whole protocol check through checked export and common-source admission.
/// Neither this nor MLIR verification establishes source-relative correctness.
mlir::LogicalResult verifyModule(mlir::Operation *root);
} // namespace protocol
} // namespace zkc
#endif
