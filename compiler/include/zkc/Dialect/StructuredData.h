#ifndef ZKC_DIALECT_STRUCTUREDDATA_H
#define ZKC_DIALECT_STRUCTUREDDATA_H

#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/IR/TypeRange.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/JSON.h"

namespace zkc {
/// Foundation /0 interchange, independent of program/0 byte spellings. These
/// conversions inspect native storage and impose expanded structural bounds.
/// Serializable vocabulary grants no operation, stage or codec admission.
llvm::Expected<llvm::json::Value> exportLogicalTypeData(mlir::Type);
llvm::Expected<llvm::json::Array> exportLogicalTypesData(mlir::TypeRange);
llvm::Expected<mlir::Type> importLogicalTypeData(mlir::MLIRContext *,
                                                 const llvm::json::Value &);
/// A list shares one expanded-work budget, including repeated native types.
/// The enclosing format owns interning, uniqueness, ordering and entry limits.
llvm::Expected<llvm::SmallVector<mlir::Type>>
importLogicalTypesData(mlir::MLIRContext *, const llvm::json::Array &);

/// Standalone /0 inventory. Entries are unique, ordered and share the same
/// expanded-work budget; enclosing inline schemas use the helpers above.
llvm::Expected<llvm::json::Value> exportLogicalTypeInventory(mlir::TypeRange);
llvm::Expected<llvm::SmallVector<mlir::Type>>
importLogicalTypeInventory(mlir::MLIRContext *, const llvm::json::Value &);

/// Catalog-kinded arguments and the rederived logical signature. The binding
/// record is [contract, arguments, implementation, inputs, outputs]. Actual
/// callable ports must agree before exporting; they are never signature
/// authority.
llvm::Expected<llvm::json::Array> exportBindingData(runtime::BindingOp);
llvm::Error checkBindingData(runtime::BindingOp, const llvm::json::Value &);
llvm::Expected<llvm::json::Array>
exportInvocationParametersData(llvm::StringRef contract,
                               mlir::ArrayAttr arguments,
                               mlir::ArrayAttr parameters);
llvm::Error checkInvocationParametersData(llvm::StringRef contract,
                                          mlir::ArrayAttr arguments,
                                          mlir::ArrayAttr parameters,
                                          const llvm::json::Value &);

/// Closed participant attribute vocabulary; unrepresented semantic attributes
/// refuse instead of falling back to printed assembly. Operation admission
/// must independently constrain which attribute names and values it owns.
llvm::Expected<llvm::json::Value> exportSemanticAttributeData(mlir::Attribute);

/// Frontend declaration trees use ArrayAttr, StringAttr, BoolAttr, ui64
/// IntegerAttr and UnitAttr (JSON null). The root must be an array. This is a
/// carrier conversion, not frontend declaration validation or elaboration.
llvm::Expected<mlir::ArrayAttr>
importDeclarationData(mlir::MLIRContext *, const llvm::json::Value &);
llvm::Expected<llvm::json::Value> exportDeclarationData(mlir::Attribute);
} // namespace zkc
#endif
