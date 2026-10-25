#ifndef ZKC_DIALECT_RUNTIME_IR_RUNTIMETYPES_TD
#define ZKC_DIALECT_RUNTIME_IR_RUNTIMETYPES_TD
include "zkc/Dialect/Runtime/IR/RuntimeDialect.td"
include "mlir/IR/AttrTypeBase.td"
// Execution views, deliberately not TokenLike types: standard CF transports
// them, while execution-profile admission checks lifetime and ownership.
def RuntimeScope : TypeDef<RuntimeDialect, "Scope"> {
  let mnemonic = "scope";
  let summary = "an active execution scope, borrowed or acquired by its profile";
  let assemblyFormat = "";
}
def RuntimeTransfer : TypeDef<RuntimeDialect, "Transfer"> {
  let mnemonic = "transfer";
  let summary = "ordered values held across scope cleanup until one handoff";
  let parameters = (ins OptionalArrayRefParameter<"::mlir::Type">:$payload);
  let assemblyFormat = "`<` (`(` $payload^ `)`)? `>`";
  let genVerifyDecl = 1;
}
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
