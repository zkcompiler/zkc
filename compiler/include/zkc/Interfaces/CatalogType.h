#ifndef ZKC_INTERFACES_CATALOGTYPE_H
#define ZKC_INTERFACES_CATALOGTYPE_H
#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/IR/Types.h"
#include "llvm/ADT/SmallVector.h"
#include <optional>
namespace zkc {
/// Transient observations of a native MLIR type. The catalog owns argument
/// kinds; the MLIR type remains the sole carrier of the application.
struct CatalogTypeApplication {
  llvm::StringRef constructor;
  llvm::SmallVector<mlir::Attribute> arguments;
};
} // namespace zkc
#include "zkc/Interfaces/CatalogType.h.inc"
#endif
