#ifndef ZKC_DIALECT_PROTOCOL_IR_ORACLEOPS_TD
#define ZKC_DIALECT_PROTOCOL_IR_ORACLEOPS_TD
include "zkc/Dialect/Protocol/IR/OracleTypes.td"
include "mlir/Interfaces/SideEffectInterfaces.td"

// An oracle send allocates an occurrence anchor. Its row count is checked
// against the data and the static kind or the declared dynamic maximum.
def OracleSendOp : Op<ProtocolDialect, "oracle_send",
    [MemoryEffects<[MemRead, MemWrite]>,
     ParentOneOf<["zkc::protocol_ir::MathematicalOp", "zkc::protocol_ir::RepeatOp"]>]> {
  let arguments = (ins AnyType:$data, UI64:$rows, StrAttr:$sender,
    StrArrayAttr:$receivers, StrAttr:$site,
    OptionalAttr<UI64Attr>:$maximum_rows);
  let results = (outs OracleHandle:$handle);
  let hasVerifier = 1;
}

// Queries are ordered protocol events, including repeated and unused reads.
// The kind, rather than this operation, determines Query and Answer.
def OracleQueryOp : Op<ProtocolDialect, "oracle_query",
    [MemoryEffects<[MemRead, MemWrite]>,
     ParentOneOf<["zkc::protocol_ir::MathematicalOp", "zkc::protocol_ir::RepeatOp"]>]> {
  let arguments = (ins OracleHandle:$handle, AnyType:$position,
                       StrAttr:$owner, StrAttr:$site);
  let results = (outs AnyType:$answer);
  let hasVerifier = 1;
}

// This only forgets an exact row-count refinement. It preserves the actual
// handle and anchor, so CSE of the same input is valid.
def OracleForgetRowsOp : Op<ProtocolDialect, "oracle_forget_rows",
    [Pure, ParentOneOf<["zkc::protocol_ir::MathematicalOp", "zkc::protocol_ir::RepeatOp"]>]> {
  let arguments = (ins OracleHandle:$input);
  let results = (outs OracleHandle:$output);
  let hasVerifier = 1;
}
#endif
