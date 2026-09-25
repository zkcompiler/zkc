#ifndef ZKC_PROTOCOL_SUPPORT_H
#define ZKC_PROTOCOL_SUPPORT_H
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Protocol/Module.h"
#include "zkc/Target/Json.h"
namespace zkc::protocol {
inline mlir::StringAttr text(mlir::Builder &b, llvm::StringRef s) {
  return b.getStringAttr(s);
}
inline llvm::StringRef attr(mlir::Operation *op, llvm::StringRef key) {
  auto a = op->getAttrOfType<mlir::StringAttr>(key);
  return a ? a.getValue() : llvm::StringRef();
}
inline mlir::Operation *
operation(mlir::OpBuilder &b, llvm::StringRef name,
          mlir::ValueRange inputs = {}, mlir::TypeRange outputs = {},
          llvm::ArrayRef<mlir::NamedAttribute> attrs = {}, unsigned regions = 0,
          std::optional<mlir::Location> location = {}) {
  mlir::OperationState state(location.value_or(b.getUnknownLoc()), name);
  state.addOperands(inputs);
  state.addTypes(outputs);
  state.addAttributes(attrs);
  for (unsigned i = 0; i < regions; ++i)
    state.addRegion();
  return b.create(state);
}
inline mlir::NamedAttribute named(mlir::Builder &b, llvm::StringRef key,
                                  mlir::Attribute value) {
  return b.getNamedAttr(key, value);
}
inline mlir::NamedAttribute named(mlir::Builder &b, llvm::StringRef key,
                                  llvm::StringRef value) {
  return named(b, key, text(b, value));
}
} // namespace zkc::protocol
#endif
