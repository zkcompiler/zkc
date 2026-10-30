#ifndef ZKC_DIALECT_DATA_LAYOUT_H
#define ZKC_DIALECT_DATA_LAYOUT_H
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "llvm/Support/JSON.h"
namespace zkc::data {
/// Decode the exact Entry schema at its interchange boundary. This is not
/// admission of source authority, capabilities or a native installation.
LayoutAttr importLayout(mlir::MLIRContext *, const llvm::json::Value &);
/// Logical Host carrier; boolean and index use their standard scalar carriers.
mlir::Type valueType(LayoutAttr);
} // namespace zkc::data
#endif
