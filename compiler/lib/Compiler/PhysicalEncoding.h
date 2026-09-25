#ifndef ZKC_COMPILER_PHYSICAL_ENCODING_H
#define ZKC_COMPILER_PHYSICAL_ENCODING_H
#include "zkc/Compiler/Library.h"
namespace zkc {
// Export-only helper: the operation has already passed native verification.
llvm::Expected<llvm::json::Value>
physicalDescriptor(mlir::Operation *, const SourceLibraryInterface &);
} // namespace zkc
#endif
