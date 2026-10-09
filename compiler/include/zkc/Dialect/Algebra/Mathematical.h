#ifndef ZKC_DIALECT_ALGEBRA_MATHEMATICAL_H
#define ZKC_DIALECT_ALGEBRA_MATHEMATICAL_H

#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Types.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include <cstdint>

namespace zkc::algebra {
// Finite data formation; arrays acquire polynomial meaning only through poly.
inline constexpr uint64_t MaximumArrayLength = 1048576;
bool isFieldArray(mlir::Type type);
bool isCanonicalFieldLiteral(llvm::StringRef field, llvm::StringRef value);
/// The one admitted scalar field of a checked pointwise map signature, or a
/// null type. Rowwise inputs and the single result are dynamic vectors
/// (`tensor<?xF>`); the other inputs are scalars `F`. At least one input must
/// be rowwise. This is formation only; the scalar formula is checked by its
/// realization.
mlir::Type mapField(mlir::FunctionType type, llvm::ArrayRef<bool> rowwise);
} // namespace zkc::algebra
#endif
