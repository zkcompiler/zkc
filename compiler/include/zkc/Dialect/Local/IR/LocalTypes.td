#ifndef ZKC_DIALECT_LOCAL_IR_LOCALTYPES_TD
#define ZKC_DIALECT_LOCAL_IR_LOCALTYPES_TD

include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/Local/IR/LocalDialect.td"
include "zkc/Dialect/TypeBindings.td"
def VariantSyntax : ZKC_SpecialType<"variant">;

def Capability : TypeDef<LocalDialect, "Capability"> {
  let mnemonic = "capability";
  let parameters = (ins StringRefParameter<"Installed capability kind">:$kind);
  let assemblyFormat = "`<` $kind `>`";
}

def Opaque : TypeDef<LocalDialect, "Opaque"> {
  let mnemonic = "opaque";
  let parameters = (ins StringRefParameter<"Declared data type">:$name);
  let assemblyFormat = "`<` $name `>`";
}

def Variant : TypeDef<LocalDialect, "Variant"> {
  let mnemonic = "variant";
  let parameters = (ins StringRefParameter<"Canonical complete logical descriptor">:$descriptor);
  let assemblyFormat = "`<` $descriptor `>`";
}

#endif
