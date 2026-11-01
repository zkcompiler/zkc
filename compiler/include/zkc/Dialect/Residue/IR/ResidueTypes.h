#ifndef ZKC_DIALECT_RESIDUE_IR_RESIDUETYPES_H
#define ZKC_DIALECT_RESIDUE_IR_RESIDUETYPES_H
#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/OpImplementation.h"
#include "zkc/Dialect/Residue/IR/ResidueDialect.h"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Residue/IR/residueTypes.h.inc"
namespace zkc::residue {
inline constexpr unsigned MaximumWordWidth = 4096;
// Only scalars and ordinary ranked tensors participate. Standard vectors are
// formed after representation lowering, with builtin integer elements.
ValueType getElementType(mlir::Type type);
} // namespace zkc::residue
#endif
