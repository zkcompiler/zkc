#ifndef ZKC_TRANSFORMS_MATHEMATICAL_H
#define ZKC_TRANSFORMS_MATHEMATICAL_H
#include "mlir/IR/BuiltinOps.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
namespace zkc::mathematical {
/// Admit the whole mathematical module, then check polynomial observations in
/// selected pure helpers even when no execution path calls them. Expansion and
/// degree checks use bounded scratch copies without simplification or
/// execution; the supplied original is unchanged. Names must be distinct
/// existing helpers.
mlir::LogicalResult
verifyHelperObservations(mlir::ModuleOp original,
                         llvm::ArrayRef<llvm::StringRef> helpers);

/// Source-formula linkage and observation admission on an already verified
/// immutable mathematical original. Roots derive from native declaration keys;
/// one shared work budget covers inventory, uses, clones and expansion. Full
/// logical schema/revision agreement is checked at the source interface
/// boundary.
llvm::Error checkFormulaDefinitions(mlir::ModuleOp, uint64_t &remaining);

/// Check the six selected realization rules against actual generated bodies.
/// Preserves ordered checks under the declared primitive contracts and
/// sufficient capacity. Does not prove native kernel implementations.
mlir::LogicalResult verifyPolynomialRecipesPreserved(mlir::ModuleOp original,
                                                     mlir::ModuleOp candidate);
mlir::LogicalResult expandPolynomialRecipes(mlir::ModuleOp module);

/// Realize admitted data-signature math helpers through the common polynomial
/// and calculation lowerers. Calls remain ordered and expand with local.apply.
mlir::LogicalResult expandMathRealizations(mlir::ModuleOp module);
/// Structural containment check, not an independent proof of the math lowerers.
/// Checks retained declarations, data-only recipes and binding accounting.
mlir::LogicalResult verifyMathRealizationsPreserved(mlir::ModuleOp original,
                                                    mlir::ModuleOp candidate);

/// Replace each algebra.map_realize with an ordinary local.func of the same
/// signature. The helper is expanded into a detached scalar formula and
/// admitted by the shared Ring view, including unused operations. The body
/// checks every rowwise input's length against the first before arithmetic,
/// then applies the live formula with O(formula) checked vector operations.
/// Calls remain ordered local.apply occurrences.
mlir::LogicalResult expandMapRealizations(mlir::ModuleOp module);
/// Independent pattern check of each generated body against the formula
/// derived again from the retained original: shape guards, operand modes,
/// broadcasts, field operations, return value, bindings and the declaration
/// inventory. It claims equal values and shape refusals under sufficient
/// resources under the declared primitive contracts, not equal resource
/// exhaustion.
mlir::LogicalResult verifyMapRealizationsPreserved(mlir::ModuleOp original,
                                                   mlir::ModuleOp candidate);
/// Admission of every map formula on an immutable original, using bounded
/// scratch expansion. Refusals keep their algebra-map identifiers.
llvm::Error checkMapFormulas(mlir::ModuleOp original, uint64_t &remaining);

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
