#ifndef ZKC_ANALYSIS_RESIDUEARITHMETIC_H
#define ZKC_ANALYSIS_RESIDUEARITHMETIC_H

#include "mlir/IR/BuiltinOps.h"

namespace zkc::residue {
/// Independently interpret one closed scalar residue function and its actual
/// Arith candidate. Prove nonwrapping ranges, canonical results and exact
/// lifts; compare modular expressions without invoking a producer or rewrite
/// pass. The closed profile bounds instructions and widths and checks unused
/// code. This is correspondence under canonical input admission, not execution
/// or a resource judgment. Recheck after mutation; no approval marker is
/// attached.
mlir::LogicalResult verifyArithmetic(mlir::ModuleOp source,
                                     mlir::ModuleOp candidate);
/// Consume the actual candidate as a closed canonical residue function. This
/// numerical profile has residue inputs and one residue result. The returned
/// expression is reconstructed from the word reader, including its normalized
/// constants and sharing; it is not a clone of the original formula.
mlir::OwningOpRef<mlir::ModuleOp> consumeArithmetic(mlir::ModuleOp source,
                                                    mlir::ModuleOp candidate);
} // namespace zkc::residue
#endif
