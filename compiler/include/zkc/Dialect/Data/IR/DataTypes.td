#ifndef ZKC_DIALECT_DATA_IR_DATATYPES_TD
#define ZKC_DIALECT_DATA_IR_DATATYPES_TD
include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/Data/IR/DataDialect.td"
def Sequence : TypeDef<DataDialect, "Sequence"> {
  let mnemonic = "sequence";
  let summary = "immutable ordered values with a runtime length";
  let parameters = (ins "::mlir::Type":$elementType);
  let assemblyFormat = "`<` $elementType `>`";
  let genVerifyDecl = 1;
}
#endif
