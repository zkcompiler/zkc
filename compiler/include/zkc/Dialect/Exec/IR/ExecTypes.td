#ifndef ZKC_DIALECT_EXEC_IR_EXECTYPES_TD
#define ZKC_DIALECT_EXEC_IR_EXECTYPES_TD
include "zkc/Dialect/Exec/IR/ExecDialect.td"
include "mlir/IR/AttrTypeBase.td"
def ExecStop : TypeDef<ExecDialect, "Stop"> {
  let mnemonic = "stop";
  let summary = "terminal cause interpreted in the residual execution state";
  let assemblyFormat = "";
}
def ExecOutcome : TypeDef<ExecDialect, "Outcome"> {
  let mnemonic = "outcome";
  let summary = "returned payload or terminal stop, never an ordinary value";
  let parameters = (ins OptionalArrayRefParameter<"::mlir::Type">:$payload);
  let assemblyFormat = "`<` (`(` $payload^ `)`)? `>`";
}
#endif
