#ifndef ZKC_DIALECT_PLAN_IR_PHYSICAL_H
#define ZKC_DIALECT_PLAN_IR_PHYSICAL_H
#include "zkc/Interfaces/SourceLibrary.h"
namespace zkc {
/// The first physical profile changes scalar values, retaining logical domain
/// indices in the external ABI. Tables and points use their existing carriers.
mlir::Type physicalType(mlir::Type);
mlir::Type logicalType(mlir::Type);
bool isPhysicalProgram(mlir::Operation *);
mlir::LogicalResult verifyPhysicalOperationContext(mlir::Operation *);
} // namespace zkc
#endif
