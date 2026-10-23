#pragma once

#include "Arithmetic.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/Support/LogicalResult.h"

namespace zkc::heir {
// Interpret the actual admitted SSA for a separately authored source or native
// execution reader. Canonical input tensors remain an explicit precondition.
mlir::FailureOr<ArithmeticMeaning> readArithmetic(mlir::ModuleOp module,
                                                  uint64_t &remaining,
                                                  bool *exhausted = nullptr);
// Reads the actual source and candidate separately. Acceptance establishes the
// admitted ring-expression comparison, conditional on canonical tensor inputs;
// it does not validate lowered machine code or native resource admission.
mlir::LogicalResult compareArithmetic(mlir::ModuleOp source,
                                      mlir::ModuleOp candidate,
                                      uint64_t *remaining = nullptr,
                                      bool *exhausted = nullptr);
enum class PlacementStatus { Unsupported, Unavailable, Mismatch, Verified };
// Returns only a separately checked candidate. The caller retains source and
// owns fallback and any subsequent executable lowering/admission.
mlir::FailureOr<mlir::OwningOpRef<mlir::ModuleOp>>
placeTransforms(mlir::ModuleOp source, PlacementStatus *status = nullptr,
                uint64_t *remaining = nullptr);
} // namespace zkc::heir
