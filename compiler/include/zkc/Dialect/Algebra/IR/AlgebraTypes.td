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

def Group : TypeDef<AlgebraDialect, "Group"> {
  let mnemonic = "group";
  let parameters = (ins StringRefParameter<"Group domain">:$domain);
  let assemblyFormat = "`<` $domain `>`";
}

#endif
