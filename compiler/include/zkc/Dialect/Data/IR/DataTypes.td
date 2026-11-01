#ifndef ZKC_DIALECT_DATA_IR_DATATYPES_TD
#define ZKC_DIALECT_DATA_IR_DATATYPES_TD
include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/Data/IR/DataDialect.td"
include "zkc/Dialect/Data/IR/DataAttrs.td"
include "zkc/Interfaces/Collection.td"
include "zkc/Dialect/TypeBindings.td"
def VariantSyntax : ZKC_SpecialType<"variant">;
def Variant : TypeDef<DataDialect, "Variant"> {
  let mnemonic = "variant";
  let summary = "nominal sum with ordered structural alternatives and payloads";
  let parameters = (ins "::zkc::data::IdentityAttr":$identity,
    ArrayRefParameter<"::zkc::data::AlternativeAttr">:$alternatives);
  let assemblyFormat = "`<` $identity `,` `[` $alternatives `]` `>`";
  let genVerifyDecl = 1;
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
  let parameters = (ins "::zkc::data::LayoutAttr":$layout);
  let assemblyFormat = "`<` $layout `>`";
  let genVerifyDecl = 1;
}
def FieldVector : TypeDef<DataDialect, "FieldVector",
    [DeclareTypeInterfaceMethods<CollectionTypeInterface>]> {
  let mnemonic = "field_vector";
  let summary = "ordered field elements with a runtime length";
  let parameters = (ins StringRefParameter<"Resolved field">:$domain);
  let assemblyFormat = "`<` $domain `>`";
  let genVerifyDecl = 1;
}

def GroupVector : TypeDef<DataDialect, "GroupVector",
    [DeclareTypeInterfaceMethods<CollectionTypeInterface>]> {
  let mnemonic = "group_vector";
  let summary = "ordered group elements with a runtime length";
  let parameters = (ins StringRefParameter<"Group domain">:$domain);
  let assemblyFormat = "`<` $domain `>`";
}

def Indices : TypeDef<DataDialect, "Indices",
    [DeclareTypeInterfaceMethods<CollectionTypeInterface>]> {
  let mnemonic = "indices";
  let summary = "ordered unsigned 64-bit indices with a runtime length";
}

def FieldMatrix : TypeDef<DataDialect, "FieldMatrix",
    [DeclareTypeInterfaceMethods<CollectionTypeInterface>]> {
  let mnemonic = "field_matrix";
  let summary = "field elements with runtime row and column counts";
  let parameters = (ins StringRefParameter<"Resolved field">:$domain);
  let assemblyFormat = "`<` $domain `>`";
  let genVerifyDecl = 1;
}

def FieldArray : TypeDef<DataDialect, "FieldArray",
    [DeclareTypeInterfaceMethods<CollectionTypeInterface>]> {
  let mnemonic = "field_array";
  let summary = "ordered field elements with an intrinsic exact length";
  let parameters = (ins StringRefParameter<"Resolved field">:$domain,
                        "uint64_t":$length);
  let assemblyFormat = "`<` $domain `,` $length `>`";
  let genVerifyDecl = 1;
}

def FixedVector : TypeDef<DataDialect, "FixedVector",
    [DeclareTypeInterfaceMethods<CollectionTypeInterface>]> {
  let mnemonic = "fixed_vector";
  let summary = "one logical bulk value with an exact element type and length";
  let parameters = (ins "::mlir::Type":$elementType, "uint64_t":$length);
  let assemblyFormat = "`<` $elementType `,` $length `>`";
  let genVerifyDecl = 1;
}

#endif
