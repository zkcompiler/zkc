#ifndef ZKC_DIALECT_ORACLE_IR_ORACLETYPES_TD
#define ZKC_DIALECT_ORACLE_IR_ORACLETYPES_TD

include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/Oracle/IR/OracleDialect.td"

def OracleObject : TypeDef<OracleDialect, "OracleObject"> {
  let mnemonic = "object";
  let summary = "nominal row authentication object or ordered custody collection";
  let parameters = (ins StringRefParameter<"Row commitment contract">:$scheme,
    StringRefParameter<"Object kind">:$kind);
  let assemblyFormat = "`<` $scheme `,` $kind `>`";
}

#endif
