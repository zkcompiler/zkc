#ifndef ZKC_DIALECT_PROTOCOL_IR_PROTOCOLTYPES_TD
#define ZKC_DIALECT_PROTOCOL_IR_PROTOCOLTYPES_TD

include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/Protocol/IR/ProtocolDialect.td"

def ServiceReference : TypeDef<ProtocolDialect, "ServiceReference"> {
  let mnemonic = "service_ref";
  let parameters = (ins StringRefParameter<"Installed service contract">:$contract);
  let assemblyFormat = "`<` $contract `>`";
}

#endif
