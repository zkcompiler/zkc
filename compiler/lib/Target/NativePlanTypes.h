#ifndef ZKC_TARGET_NATIVE_PLAN_TYPES_H
#define ZKC_TARGET_NATIVE_PLAN_TYPES_H

#include "mlir/IR/Types.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"

namespace zkc::target {
/// Native formation, independent of CPU availability and byte profile limits.
llvm::Error checkPhysicalType(mlir::Type);
llvm::Expected<mlir::Type>
formPhysicalType(mlir::Type logical, llvm::StringRef representation,
                 llvm::ArrayRef<mlir::Type> children);
llvm::Expected<mlir::Type> defaultPlanType(mlir::Type logical);
llvm::StringRef planTypeConstructor(mlir::Type);
llvm::Expected<llvm::SmallVector<mlir::Type>> planLogicalChildren(mlir::Type);

} // namespace zkc::target
#endif
