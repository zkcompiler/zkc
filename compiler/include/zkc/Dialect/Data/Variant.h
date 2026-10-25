#ifndef ZKC_DIALECT_DATA_VARIANT_H
#define ZKC_DIALECT_DATA_VARIANT_H
#include "mlir/IR/Types.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Error.h"
namespace zkc::data {
/// Exact flattened payload of a declared nominal alternative, including the
/// installed child representations when the carrier is represented.
llvm::Expected<llvm::SmallVector<mlir::Type>>
variantPayloadTypes(mlir::Type carrier, llvm::StringRef alternative);
} // namespace zkc::data
#endif
