#ifndef ZKC_DIALECT_DATA_IR_DATATYPES_TD
#define ZKC_DIALECT_DATA_IR_DATATYPES_TD
include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/Data/IR/DataDialect.td"
include "zkc/Interfaces/Collection.td"
include "zkc/Dialect/TypeBindings.td"
def VariantSyntax : ZKC_SpecialType<"variant">;
def Variant : TypeDef<DataDialect, "Variant"> {
  let mnemonic = "variant";
  let summary = "nominal sum with an exact closed logical payload descriptor";
  let parameters = (ins StringRefParameter<"Canonical complete logical descriptor">:$descriptor);
  let assemblyFormat = "`<` $descriptor `>`";
}
def Bytes : TypeDef<DataDialect, "Bytes",
    [DeclareTypeInterfaceMethods<CollectionTypeInterface>]> {
  let mnemonic = "bytes";
  let summary = "immutable byte string with a runtime length";
  let assemblyFormat = "";
}
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
def DataValue : TypeDef<DataDialect, "Value"> {
  let mnemonic = "value";
  let summary = "nominal source value with an exact logical schema";
  let parameters = (ins StringRefParameter<"Canonical logical schema">:$schema);
  let assemblyFormat = "`<` $schema `>`";
}
#endif
