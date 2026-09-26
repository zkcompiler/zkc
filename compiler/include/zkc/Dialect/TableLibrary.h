#ifndef ZKC_DIALECT_TABLELIBRARY_H
#define ZKC_DIALECT_TABLELIBRARY_H
#include "mlir/IR/DialectRegistry.h"
namespace zkc {
void registerTableLibrary(mlir::DialectRegistry &);
} // namespace zkc
#endif
