#pragma once

#include "mlir/IR/BuiltinOps.h"
#include "mlir/Support/LogicalResult.h"

namespace zkc::heir {
// Reads the actual source and candidate separately. Acceptance establishes the
// admitted ring-expression comparison, conditional on canonical tensor inputs;
// it does not validate lowered machine code or native resource admission.
mlir::LogicalResult compareArithmetic(mlir::ModuleOp source,
                                      mlir::ModuleOp candidate);
// Returns only a separately checked candidate. The caller retains source and
// owns fallback and any subsequent executable lowering/admission.
mlir::FailureOr<mlir::OwningOpRef<mlir::ModuleOp>>
placeTransforms(mlir::ModuleOp source);
} // namespace zkc::heir
