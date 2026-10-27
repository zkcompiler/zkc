#ifndef ZKC_TRANSFORMS_MATHEMATICAL_H
#define ZKC_TRANSFORMS_MATHEMATICAL_H
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Transforms/MathematicalSelection.h"
#include "zkc/Transforms/MathematicalTrace.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
namespace zkc::mathematical {
/// Preserve the start of one selected expanded application. Input indices
/// refer to the callee's original argument list, before role substitution.
/// Selection comes from a checked construction; expansion and correspondence
/// independently validate that the exact occurrence and shared inputs exist.
struct ApplicationStart {
  std::string protocol, site;
  llvm::SmallVector<unsigned> inputs;
};
/// Prepare an owned candidate without modifying the source. Realize polynomial
/// recipes, expand protocol applications, then prepare participant mathematics.
/// Preserve scoped definitions and finite requests for executable selection.
/// Selected
/// application starts are semantic construction inputs, not pass options.
/// Expansion and correspondence check each selection before publication.
mlir::OwningOpRef<mlir::ModuleOp>
prepareProtocol(mlir::ModuleOp source, bool simplify = true,
                MathematicalSelectionPolicy policy = {},
                llvm::ArrayRef<ApplicationStart> starts = {},
                RealizationTrace *trace = nullptr);

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

/// Independently read original scoped execution against the actual scoped
/// numerical candidate. Mathematical and finite requests retain their original
/// callbacks, equations and policies; unchanged context stays exact. Explicit
/// implementation requests constrain replacement as well as final binding
/// selection. Optional comparison capacity is typed and attributable; a
/// semantic mismatch never authorizes retry.
mlir::LogicalResult verifyNumericalLowering(
    mlir::ModuleOp original, mlir::ModuleOp candidate,
    MathematicalSelectionPolicy policy = {},
    llvm::ArrayRef<std::pair<std::string, std::string>> selections = {},
    RealizationWork *work = nullptr, VerificationDecision *outcome = nullptr);

// Closed, bounded checks on actual source/candidate pairs. Keep the original
// frozen and verify both subjects before calling. Preparation and projection
// use virtual substitutions and role-indexed value terms; participant rewrites
// use explicit Boolean/polynomial laws. Participant -> Exec separately checks
// demand placement and Kernel formation. Kernel realization has its own
// correspondence check. Exec -> Physical checks participant data flow
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
/// Lowering of participant mathematics is checked against the calculation
/// schedule of `policy`.
mlir::LogicalResult
verifyProjectionPreserved(mlir::ModuleOp original, mlir::ModuleOp candidate,
                          MathematicalSelectionPolicy policy = {});
mlir::LogicalResult verifyProtocolPreparationPreserved(mlir::Operation *before,
                                                       mlir::Operation *after);
mlir::LogicalResult verifyAuthoredLocalsPreserved(mlir::Operation *before,
                                                  mlir::Operation *after);
} // namespace zkc::mathematical
#endif
