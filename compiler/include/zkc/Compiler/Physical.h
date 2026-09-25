#ifndef ZKC_COMPILER_PHYSICAL_H
#define ZKC_COMPILER_PHYSICAL_H
#include "zkc/Compiler/Library.h"
namespace mlir {
class ModuleOp;
}
namespace zkc {
/// The first physical profile changes scalar values, retaining logical domain
/// indices in the external ABI. Tables and points use their existing carriers.
mlir::Type physicalType(mlir::Type);
mlir::Type logicalType(mlir::Type);
bool isPhysicalProgram(mlir::Operation *);
mlir::LogicalResult verifyPhysicalOperationContext(mlir::Operation *);
mlir::LogicalResult lowerToPhysical(mlir::ModuleOp, llvm::StringRef mode);
} // namespace zkc
#endif
