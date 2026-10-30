#ifndef ZKC_DIALECT_DATA_VARIANT_H
#define ZKC_DIALECT_DATA_VARIANT_H
#include "mlir/IR/Types.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Error.h"
namespace zkc::data {
/// Translation at neutral declaration and program-format boundaries. Internal
/// operations inspect the structured identity and payload types directly.
IdentityAttr importVariantIdentity(mlir::MLIRContext *,
                                   const llvm::json::Value &);
llvm::json::Value exportVariantIdentity(IdentityAttr);
VariantType importVariantType(mlir::MLIRContext *,
                              const protocol::VariantDescriptor &);
/// Exact flattened payload of a declared nominal alternative, including the
/// installed child representations when the carrier is represented.
llvm::Expected<llvm::SmallVector<mlir::Type>>
variantPayloadTypes(mlir::Type carrier, llvm::StringRef alternative);
} // namespace zkc::data
#endif
