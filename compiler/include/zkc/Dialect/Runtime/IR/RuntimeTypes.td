#ifndef ZKC_DIALECT_RUNTIME_IR_RUNTIMETYPES_TD
#define ZKC_DIALECT_RUNTIME_IR_RUNTIMETYPES_TD
include "zkc/Dialect/Runtime/IR/RuntimeDialect.td"
include "mlir/IR/AttrTypeBase.td"
def RuntimeQuotientMatrix : TypeDef<RuntimeDialect, "QuotientMatrix"> {
  let mnemonic = "quotient_matrix";
  let summary = "immutable prepared quotient matrix with exact ring and lift plan";
  let assemblyFormat = "";
}
#endif
