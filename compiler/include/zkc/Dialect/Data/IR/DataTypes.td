#ifndef ZKC_DIALECT_DATA_IR_DATATYPES_TD
#define ZKC_DIALECT_DATA_IR_DATATYPES_TD
include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/Data/IR/DataDialect.td"
include "zkc/Interfaces/Collection.td"
def Domain : TypeDef<DataDialect, "Domain"> {
  let mnemonic = "domain";
  let summary = "preparation-only ordered finite item parameter list";
  let parameters = (ins ArrayRefParameter<"::mlir::Type">:$itemTypes);
  let assemblyFormat = "`<` $itemTypes `>`";
  let genVerifyDecl = 1;
}
def Sequence : TypeDef<DataDialect, "Sequence",
    [DeclareTypeInterfaceMethods<CollectionTypeInterface>]> {
  let mnemonic = "sequence";
  let summary = "immutable ordered values with a runtime length";
  let parameters = (ins "::mlir::Type":$elementType);
  let assemblyFormat = "`<` $elementType `>`";
  let genVerifyDecl = 1;
}
#endif
