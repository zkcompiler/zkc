#ifndef ZKC_DIALECT_PCS_IR_PCSTYPES_TD
#define ZKC_DIALECT_PCS_IR_PCSTYPES_TD

include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/PCS/IR/PCSDialect.td"

def PCSObject : TypeDef<PCSDialect, "Object"> {
  let mnemonic = "object";
  let parameters = (ins StringRefParameter<"PCS contract">:$scheme,
    StringRefParameter<"Object kind">:$kind);
  let assemblyFormat = "`<` $scheme `,` $kind `>`";
}

#endif
