#ifndef ZKC_DIALECT_PHYSICAL_ENCODING_H
#define ZKC_DIALECT_PHYSICAL_ENCODING_H
#include "zkc/Interfaces/SourceLibrary.h"
namespace zkc {
// Export-only helper: the operation has already passed native verification.
llvm::Expected<llvm::json::Value>
physicalDescriptor(mlir::Operation *, const SourceLibraryInterface &);
} // namespace zkc
#endif
