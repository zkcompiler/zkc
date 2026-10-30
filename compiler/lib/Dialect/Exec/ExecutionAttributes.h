#ifndef ZKC_DIALECT_EXEC_EXECUTION_ATTRIBUTES_H
#define ZKC_DIALECT_EXEC_EXECUTION_ATTRIBUTES_H

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Interfaces/CallInterfaces.h"

namespace zkc::exec::detail {
// A formation-checked function/call may materialize ABI-sized dictionaries
// through standard MLIR interfaces. Check arity here as well: ordinary
// func.call formation does not enforce the dictionary-array lengths.
// Empty dictionaries add no semantics;
// nonempty annotations need an explicit reader/byte contract and must not be
// silently discarded. This is a structural predicate shared by independent
// body readers, not their control or correspondence implementation.
inline bool
hasOnlyExecutionAttributes(mlir::Operation *op,
                           llvm::ArrayRef<llvm::StringRef> allowed = {}) {
  if (!op)
    return false;
  for (mlir::NamedAttribute attr : op->getAttrs()) {
    auto name = attr.getName().getValue();
    if (llvm::is_contained(allowed, name))
      continue;
    if (name != "arg_attrs" && name != "res_attrs")
      return false;
    unsigned ports;
    if (auto function = mlir::dyn_cast<mlir::func::FuncOp>(op)) {
      auto type = function.getFunctionType();
      ports = name == "arg_attrs" ? type.getNumInputs() : type.getNumResults();
    } else if (auto call = mlir::dyn_cast<mlir::CallOpInterface>(op)) {
      ports = name == "arg_attrs" ? call.getArgOperands().size()
                                  : op->getNumResults();
    } else
      return false;
    auto dictionaries = mlir::dyn_cast<mlir::ArrayAttr>(attr.getValue());
    if (!dictionaries || dictionaries.size() != ports ||
        llvm::any_of(dictionaries, [](mlir::Attribute value) {
          auto dictionary = mlir::dyn_cast<mlir::DictionaryAttr>(value);
          return !dictionary || !dictionary.empty();
        }))
      return false;
  }
  return true;
}
} // namespace zkc::exec::detail
#endif
