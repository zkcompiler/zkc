#ifndef ZKC_DIALECT_ALGEBRA_IR_ALGEBRATYPES_TD
#define ZKC_DIALECT_ALGEBRA_IR_ALGEBRATYPES_TD

include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/Algebra/IR/AlgebraDialect.td"

def Field : TypeDef<AlgebraDialect, "Field"> {
  let mnemonic = "field";
  let summary = "resolved field element";
  let parameters = (ins StringRefParameter<"Resolved field">:$domain);
  let assemblyFormat = "`<` $domain `>`";
  let genVerifyDecl = 1;
}

def FixedVector : TypeDef<AlgebraDialect, "FixedVector"> {
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
