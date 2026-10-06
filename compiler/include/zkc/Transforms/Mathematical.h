#ifndef ZKC_TRANSFORMS_MATHEMATICAL_H
#define ZKC_TRANSFORMS_MATHEMATICAL_H
#include "mlir/IR/BuiltinOps.h"
namespace zkc::mathematical {
/// Check the six selected realization rules against actual generated bodies.
/// Preserves ordered checks under the declared primitive contracts and
/// sufficient capacity. Does not prove native kernel implementations.
mlir::LogicalResult verifyPolynomialRecipesPreserved(mlir::ModuleOp original,
                                                     mlir::ModuleOp candidate);
mlir::LogicalResult expandPolynomialRecipes(mlir::ModuleOp module);

// Closed, bounded checks on actual source/candidate pairs. Keep the original
// frozen and verify both subjects before calling. Preparation and projection
// use virtual substitutions and role-indexed value terms; participant rewrites
// use explicit Boolean/polynomial laws. Participant -> Exec separately checks
// demand placement and recipes. Exec -> Physical checks participant data flow
// and projection metadata only; it does not validate local materialization.
// Use protocol::lowerPhysical or SelectPhysical for the complete checked edge;
// their internal materialization check also covers local bodies and bindings.
// Storage has its own check. These checks assume the
// declared operation meanings and sufficient realization capacity, not equality
// at arbitrary native resource caps. Supported edges: Protocol -> Participant,
// Participant -> Exec, Exec -> Physical, and same-profile Participant, Exec or
// Physical. Same-profile Exec and Physical require structural identity,
// ignoring locations and SSA names. Materialization and storage rewrites use
// their dedicated checks. Skipped or backward edges refuse. Executable inputs
// without projection records acquire no common-source claim.
mlir::LogicalResult verifyProjectionPreserved(mlir::ModuleOp original,
                                              mlir::ModuleOp candidate);
mlir::LogicalResult verifyProtocolPreparationPreserved(mlir::Operation *before,
                                                       mlir::Operation *after);
mlir::LogicalResult verifyAuthoredLocalsPreserved(mlir::Operation *before,
                                                  mlir::Operation *after);
} // namespace zkc::mathematical
#endif
