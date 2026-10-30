#ifndef ZKC_ANALYSIS_COMPUTATIONMEANING_H
#define ZKC_ANALYSIS_COMPUTATIONMEANING_H

#include "mlir/IR/Operation.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Dialect/Algebra/IR/AlgebraAttrs.h"

namespace zkc::finite {
/// Exact logical meaning, including explicitly constrained implementations.
/// Unknown attributes and mismatched nominal ports have no semantic facet.
/// No serialized analysis attribute is consulted.
const protocol::ComputationContract *semantics(mlir::Operation *operation);
/// Meaning alone does not authorize rebinding an explicit implementation.
bool replaceable(mlir::Operation *operation);
algebra::FieldLiteralAttr fieldConstant(mlir::Operation *operation);

} // namespace zkc::finite
#endif
