#ifndef ZKC_DIALECT_ALGEBRA_MATHEMATICAL_H
#define ZKC_DIALECT_ALGEBRA_MATHEMATICAL_H

#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Types.h"
#include "mlir/Support/LogicalResult.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringRef.h"
#include <cstdint>
#include <utility>

namespace mlir {
class SymbolTableCollection;
} // namespace mlir
namespace zkc::algebra {
// Finite data formation; arrays acquire polynomial meaning only through poly.
inline constexpr uint64_t MaximumArrayLength = 1048576;
bool isFieldArray(mlir::Type type);
} // namespace zkc::algebra
#endif
