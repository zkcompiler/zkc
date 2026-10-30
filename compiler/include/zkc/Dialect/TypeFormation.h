#ifndef ZKC_DIALECT_TYPEFORMATION_H
#define ZKC_DIALECT_TYPEFORMATION_H
#include "mlir/IR/Diagnostics.h"
#include "mlir/IR/Types.h"
#include "zkc/Interfaces/CatalogType.h"
namespace zkc {
struct LogicalTypePermissions {
  bool copy = true, drop = true;
};
/// Check a closed native logical type directly through its catalog observation
/// or its nominal variant structure. Count expanded children and metadata.
/// This grants neither stage admission nor availability of an encoding or
/// representation. Executable and interchange boundaries check those
/// separately.
mlir::LogicalResult
verifyLogicalType(llvm::function_ref<mlir::InFlightDiagnostic()> emit,
                  mlir::Type type,
                  LogicalTypePermissions *permissions = nullptr);
/// Verify a represented value's exact logical instance and ordered physical
/// children directly. Does not select defaults, authorize an implementation,
/// or impose byte-profile limits. Also used before interning the parent.
mlir::LogicalResult
verifyRepresentedType(llvm::function_ref<mlir::InFlightDiagnostic()> emit,
                      mlir::Type logical, llvm::StringRef representation,
                      llvm::ArrayRef<mlir::Type> children);
/// Form either a logical value or its exact represented carrier. Callers must
/// separately enforce uniform stage and their supported operation profile.
mlir::LogicalResult
verifyValueType(llvm::function_ref<mlir::InFlightDiagnostic()> emit,
                mlir::Type type);
/// Erase only the outer representation. This operation grants no formation,
/// stage admission or permission to reinterpret a value at runtime.
mlir::Type logicalValueType(mlir::Type type);
/// Verify constructor parameters before interning the parent native type.
/// This avoids recursively constructing a type from its own verifier.
mlir::LogicalResult verifyLogicalTypeApplication(
    llvm::function_ref<mlir::InFlightDiagnostic()> emit,
    mlir::MLIRContext *context, const CatalogTypeApplication &application);
/// Construct from formed typed arguments using the declared native owner.
/// Missing loaded types and ambiguous or inexact observations are refusals.
/// Never loads dialects or encodes a neutral type spelling.
mlir::Type
constructLogicalType(llvm::function_ref<mlir::InFlightDiagnostic()> emit,
                     mlir::MLIRContext *context,
                     const CatalogTypeApplication &application);
} // namespace zkc
#endif
