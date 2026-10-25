#ifndef ZKC_DIALECT_RUNTIME_IR_RUNTIMETYPES_TD
#define ZKC_DIALECT_RUNTIME_IR_RUNTIMETYPES_TD
include "zkc/Dialect/Runtime/IR/RuntimeDialect.td"
include "mlir/IR/AttrTypeBase.td"
def Capability : TypeDef<RuntimeDialect, "Capability"> {
  let mnemonic = "capability";
  let summary = "logical resource kind whose authority is checked by the active runtime";
  let parameters = (ins StringRefParameter<"Installed capability kind">:$kind);
  let assemblyFormat = "`<` $kind `>`";
}
def RepresentedValue : TypeDef<RuntimeDialect, "Represented"> {
  let mnemonic = "represented";
  let summary = "logical value with an exact installed representation and child layouts";
  let parameters = (ins TypeParameter<"::mlir::Type", "Logical type">:$logical,
    StringRefParameter<"Installed representation">:$representation,
    OptionalArrayRefParameter<"::mlir::Type">:$children);
  let hasCustomAssemblyFormat = 1;
}
def RuntimeQuotientMatrix : TypeDef<RuntimeDialect, "QuotientMatrix"> {
  let mnemonic = "quotient_matrix";
  let summary = "immutable prepared quotient matrix with exact ring and lift plan";
  let assemblyFormat = "";
}
#endif
