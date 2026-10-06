#ifndef ZKC_DIALECT_TABLE_IR_TABLETYPES_TD
#define ZKC_DIALECT_TABLE_IR_TABLETYPES_TD

include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/Table/IR/TableDialect.td"

def Digest : TypeDef<TableDialect, "Digest"> {
  let mnemonic = "digest";
  let summary = "protocol digest";
}

def Flow : TypeDef<TableDialect, "Flow"> {
  let mnemonic = "flow";
  let summary = "protocol ordering value";
}

def Scalar : TypeDef<TableDialect, "Scalar"> {
  let mnemonic = "scalar";
  let summary = "immediate scalar or immutable prepared scalar reference";
  let parameters = (ins StringRefParameter<"Resolved field">:$domain);
  let assemblyFormat = "`<` $domain `>`";
  let genVerifyDecl = 1;
}

def Summary : TypeDef<TableDialect, "Summary"> {
  let mnemonic = "summary";
  let summary = "protocol summary";
}

#endif
