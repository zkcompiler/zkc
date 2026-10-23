#ifndef ZKC_DIALECT_ALGEBRA_IR_ALGEBRATYPES_TD
#define ZKC_DIALECT_ALGEBRA_IR_ALGEBRATYPES_TD

include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/Algebra/IR/AlgebraDialect.td"
include "zkc/Interfaces/Collection.td"

// A mathematical quotient value has no native port or serialized encoding.
def Quotient : TypeDef<AlgebraDialect, "Quotient"> {
  let mnemonic = "quotient";
  let summary = "formal element of (Z/qZ)[X]/(X^n+1)";
  let parameters = (ins "uint64_t":$modulus, "uint64_t":$degree);
  let assemblyFormat = "`<` $modulus `,` $degree `>`";
  let genVerifyDecl = 1;
}

def Field : TypeDef<AlgebraDialect, "Field"> {
  let mnemonic = "field";
  let summary = "resolved field element";
  let parameters = (ins StringRefParameter<"Resolved field">:$domain);
  let assemblyFormat = "`<` $domain `>`";
  let genVerifyDecl = 1;
}

def FieldVector : TypeDef<AlgebraDialect, "FieldVector",
    [DeclareTypeInterfaceMethods<CollectionTypeInterface>]> {
  let mnemonic = "field_vector";
  let summary = "ordered field elements with a runtime length";
  let parameters = (ins StringRefParameter<"Resolved field">:$domain);
  let assemblyFormat = "`<` $domain `>`";
  let genVerifyDecl = 1;
}

def GroupVector : TypeDef<AlgebraDialect, "GroupVector",
    [DeclareTypeInterfaceMethods<CollectionTypeInterface>]> {
  let mnemonic = "group_vector";
  let summary = "ordered group elements with a runtime length";
  let parameters = (ins StringRefParameter<"Group domain">:$domain);
  let assemblyFormat = "`<` $domain `>`";
}

def Indices : TypeDef<AlgebraDialect, "Indices",
    [DeclareTypeInterfaceMethods<CollectionTypeInterface>]> {
  let mnemonic = "indices";
  let summary = "ordered unsigned 64-bit indices with a runtime length";
}

def FieldMatrix : TypeDef<AlgebraDialect, "FieldMatrix",
    [DeclareTypeInterfaceMethods<CollectionTypeInterface>]> {
  let mnemonic = "field_matrix";
  let summary = "field elements with runtime row and column counts";
  let parameters = (ins StringRefParameter<"Resolved field">:$domain);
  let assemblyFormat = "`<` $domain `>`";
  let genVerifyDecl = 1;
}

def FieldArray : TypeDef<AlgebraDialect, "FieldArray",
    [DeclareTypeInterfaceMethods<CollectionTypeInterface>]> {
  let mnemonic = "field_array";
  let summary = "ordered field elements with an intrinsic exact length";
  let parameters = (ins StringRefParameter<"Resolved field">:$domain,
                        "uint64_t":$length);
  let assemblyFormat = "`<` $domain `,` $length `>`";
  let genVerifyDecl = 1;
}

def FixedVector : TypeDef<AlgebraDialect, "FixedVector",
    [DeclareTypeInterfaceMethods<CollectionTypeInterface>]> {
  let mnemonic = "fixed_vector";
  let summary = "one logical bulk value with an exact element type and length";
  let parameters = (ins "::mlir::Type":$elementType, "uint64_t":$length);
  let assemblyFormat = "`<` $elementType `,` $length `>`";
  let genVerifyDecl = 1;
}

def Group : TypeDef<AlgebraDialect, "Group"> {
  let mnemonic = "group";
  let parameters = (ins StringRefParameter<"Group domain">:$domain);
  let assemblyFormat = "`<` $domain `>`";
}


#endif
