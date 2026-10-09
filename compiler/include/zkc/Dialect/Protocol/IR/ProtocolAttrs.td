#ifndef ZKC_DIALECT_PROTOCOL_IR_PROTOCOLATTRS_TD
#define ZKC_DIALECT_PROTOCOL_IR_PROTOCOLATTRS_TD

include "zkc/Dialect/Protocol/IR/ProtocolDialect.td"
include "mlir/IR/EnumAttr.td"

class ProtocolEnum<string name, string description,
                   list<I32EnumAttrCase> cases>
    : I32EnumAttr<name, description, cases> {
  let genSpecializedAttr = 0;
  let cppNamespace = "::zkc::protocol_ir";
}

def ProtocolProfile : ProtocolEnum<"Profile", "protocol abstraction profile", [
  I32EnumAttrCase<"Protocol", 0, "protocol">,
  I32EnumAttrCase<"Participant", 1, "participant">,
  I32EnumAttrCase<"Exec", 3, "exec">,
  I32EnumAttrCase<"Physical", 4, "physical">
]>;


class ProtocolEnumAttr<ProtocolEnum info, string mnemonic>
    : EnumAttr<ProtocolDialect, info, mnemonic> {
  let assemblyFormat = "`<` $value `>`";
  let genVerifyDecl = 1;
}
def ProtocolProfileAttr : ProtocolEnumAttr<ProtocolProfile, "profile">;


#endif
