#ifndef ZKC_DIALECT_ALGEBRA_MATHEMATICAL_H
#define ZKC_DIALECT_ALGEBRA_MATHEMATICAL_H

#include "mlir/IR/Types.h"
#include "llvm/ADT/StringRef.h"
#include <cstdint>

namespace zkc::algebra {
// Finite data formation; arrays acquire polynomial meaning only through poly.
inline constexpr uint64_t MaximumArrayLength = 1048576;
bool isFieldArray(mlir::Type type);
bool isCanonicalFieldLiteral(llvm::StringRef field, llvm::StringRef value);
} // namespace zkc::algebra
#endif
