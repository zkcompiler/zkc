#ifndef ZKC_TRANSFORMS_RECIPEREALIZATIONS_H
#define ZKC_TRANSFORMS_RECIPEREALIZATIONS_H

#include "FiniteVerification.h"
#include "MathematicalRecipes.h"
#include "zkc/Transforms/Finite.h"
#include "zkc/Transforms/NestedContractions.h"

// Private closed-inventory overrides for checking recipe availability and
// ordered fallback. Public services use the installed inventory. These entry
// points retain the same independent checks and publication as those services.
namespace zkc::finite {
// Closed private test seam: the same producer, reader, and transaction as the
// public service, with independently bounded comparison and required reading.
mlir::LogicalResult
realizeLocalsWithLimits(mlir::ModuleOp module,
                        MathematicalSelectionPolicy policy,
                        mathematical::RealizationWork *work,
                        const mathematical::MathematicalRecipes &recipes,
                        VerificationLimits limits);
mlir::LogicalResult
realizeLocals(mlir::ModuleOp module, MathematicalSelectionPolicy policy,
              mathematical::RealizationWork *work,
              const mathematical::MathematicalRecipes &recipes);
} // namespace zkc::finite
namespace zkc::nested {
mlir::LogicalResult
rewriteFiniteCollections(mlir::ModuleOp module,
                         MathematicalSelectionPolicy policy,
                         const mathematical::MathematicalRecipes &recipes);
}

#endif
