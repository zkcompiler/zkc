#ifndef EXAMPLE_ENVELOPE_SPECIALIZATION_H
#define EXAMPLE_ENVELOPE_SPECIALIZATION_H

#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/PatternMatch.h"

namespace envelope {
/// Pattern precondition: admitted logical field additions. Only adjacent,
/// single-use, left-associated pairs match; no reordering or folding occurs.
void populateFieldSumSpecializationPatterns(mlir::RewritePatternSet &patterns);
void populateFieldSumDecompositionPatterns(mlir::RewritePatternSet &patterns);

/// Check source admission, then apply the specialization once in program order.
/// The intermediate module intentionally cannot pass checked source export.
mlir::LogicalResult specializeFieldSums(mlir::ModuleOp module);

/// Full conversion eliminates the temporary operation, then checked export
/// admits the entire restored module. Other operations still require their
/// existing export/admission checks. A failure must never be published.
mlir::LogicalResult decomposeFieldSums(mlir::ModuleOp module);
} // namespace envelope

#endif
