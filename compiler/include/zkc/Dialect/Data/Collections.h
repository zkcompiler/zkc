#ifndef ZKC_DIALECT_DATA_COLLECTIONS_H
#define ZKC_DIALECT_DATA_COLLECTIONS_H
#include "mlir/IR/Types.h"
#include <cstdint>
namespace zkc::data {
// Intrinsic array extent bound. Polynomial meaning requires a Poly operation.
inline constexpr uint64_t MaximumArrayLength = 1048576;
bool isFieldArray(mlir::Type type);
} // namespace zkc::data
#endif
