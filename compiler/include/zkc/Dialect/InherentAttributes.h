#ifndef ZKC_DIALECT_INHERENTATTRIBUTES_H
#define ZKC_DIALECT_INHERENTATTRIBUTES_H

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Operation.h"
#include "mlir/Interfaces/CallInterfaces.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringRef.h"

namespace zkc {
/// Upstream call and callable metadata: the argument and result attribute
/// dictionaries of call and callable operations, and the inlining directive of
/// func calls and functions. It is inherent, but it is not part of any profile
/// a reader represents.
inline bool isCallMetadata(mlir::Operation *op, mlir::StringAttr name) {
  if (mlir::isa<mlir::ArgAndResultAttrsOpInterface>(op) &&
      (name == "arg_attrs" || name == "res_attrs"))
    return true;
  if (auto call = mlir::dyn_cast<mlir::func::CallOp>(op))
    return name == call.getNoInlineAttrName();
  if (auto function = mlir::dyn_cast<mlir::func::FuncOp>(op))
    return name == function.getNoInlineAttrName();
  return false;
}

/// Attribute admission for readers of registered operations. The operation's
/// ODS definition owns its inherent attributes, which readers admit without
/// restating them. A discardable attribute, or call metadata, is admitted only
/// when the reader names it in `named`.
inline bool admitsAttribute(mlir::Operation *op, mlir::StringAttr name,
                            llvm::ArrayRef<llvm::StringRef> named = {}) {
  if (llvm::is_contained(named, name.getValue()))
    return true;
  auto registered = op->getRegisteredInfo();
  return registered &&
         llvm::is_contained(registered->getAttributeNames(), name) &&
         !isCallMetadata(op, name);
}
/// Whether a reader that names `named` admits every attribute of `op`.
inline bool
hasOnlyInherentAttributes(mlir::Operation *op,
                          llvm::ArrayRef<llvm::StringRef> named = {}) {
  return llvm::all_of(op->getAttrs(), [&](mlir::NamedAttribute attribute) {
    return admitsAttribute(op, attribute.getName(), named);
  });
}
} // namespace zkc

#endif
