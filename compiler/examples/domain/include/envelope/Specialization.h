#ifndef EXAMPLE_ENVELOPE_SPECIALIZATION_H
#define EXAMPLE_ENVELOPE_SPECIALIZATION_H

#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/PatternMatch.h"

namespace envelope {
/// Pattern precondition: admitted logical field additions. Only adjacent,
/// single-use, left-associated pairs match; no reordering or folding occurs.
void populateFieldSumSpecializationPatterns(mlir::RewritePatternSet &patterns);
void populateFieldSumDecompositionPatterns(mlir::RewritePatternSet &patterns);

/// Verify the native module, then specialize once in program order.
/// The temporary composite must be decomposed before native compilation.
mlir::LogicalResult specializeFieldSums(mlir::ModuleOp module);

/// Full conversion eliminates the temporary operation and verifies the entire
/// restored module. Executable compilation and export retain their own checks.
mlir::LogicalResult decomposeFieldSums(mlir::ModuleOp module);
} // namespace envelope

#endif
