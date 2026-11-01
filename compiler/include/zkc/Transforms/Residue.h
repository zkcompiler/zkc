#ifndef ZKC_TRANSFORMS_RESIDUE_H
#define ZKC_TRANSFORMS_RESIDUE_H
#include "mlir/IR/BuiltinOps.h"
namespace zkc::residue {
// Produce a private word-arithmetic candidate. The source stays immutable.
// Successful conversion is not correspondence, input admission or permission
// to execute; those consumers independently read the actual candidate.
mlir::OwningOpRef<mlir::ModuleOp> lowerArithmetic(mlir::ModuleOp source);
} // namespace zkc::residue
#endif
