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
  I32EnumAttrCase<"ProtocolExec", 2, "protocol_exec">,
  I32EnumAttrCase<"Exec", 3, "exec">,
  I32EnumAttrCase<"Physical", 4, "physical">
]>;

def ProtocolExecutionContract : ProtocolEnum<"ExecutionContract",
    "participant execution contract", [
  I32EnumAttrCase<"LegacyParticipantsV1", 0, "legacy_participants_v1">,
  I32EnumAttrCase<"Program", 2, "program">
]>;

class ProtocolEnumAttr<ProtocolEnum info, string mnemonic>
    : EnumAttr<ProtocolDialect, info, mnemonic> {
  let assemblyFormat = "`<` $value `>`";
  let genVerifyDecl = 1;
}
def ProtocolProfileAttr : ProtocolEnumAttr<ProtocolProfile, "profile">;
def ProtocolExecutionContractAttr :
    ProtocolEnumAttr<ProtocolExecutionContract, "execution_contract">;

#endif
