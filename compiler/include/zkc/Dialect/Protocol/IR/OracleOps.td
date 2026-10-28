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
     ParentOneOf<["zkc::protocol_ir::MathematicalOp", "zkc::protocol_ir::RepeatOp",
                  "zkc::protocol_ir::OracleDefinitionOp"]>]> {
  let arguments = (ins OracleHandle:$handle, AnyType:$position,
                       OptionalAttr<StrAttr>:$owner, StrAttr:$site);
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

// Executable data selection is holder-only. Relation anchor selectors have
// their own permissions and do not grant this executable operation.
def OracleContentsOp : Op<ProtocolDialect, "oracle_contents",
    [Pure, ParentOneOf<["zkc::protocol_ir::MathematicalOp", "zkc::protocol_ir::RepeatOp"]>]> {
  let arguments = (ins OracleHandle:$handle, StrAttr:$owner);
  let results = (outs AnyType:$data);
  let hasVerifier = 1;
}

def OracleSequenceEmptyOp : Op<ProtocolDialect, "oracle_sequence_empty",
    [Pure, ParentOneOf<["zkc::protocol_ir::MathematicalOp", "zkc::protocol_ir::RepeatOp"]>]> {
  let results = (outs OracleSequence:$output);
}

// Append and selection have explicit stopping bounds checks at every selected
// role. They preserve the persistent sequence and the actual selected anchor.
def OracleSequenceAppendOp : Op<ProtocolDialect, "oracle_sequence_append",
    [MemoryEffects<[MemRead, MemWrite]>,
     ParentOneOf<["zkc::protocol_ir::MathematicalOp", "zkc::protocol_ir::RepeatOp"]>]> {
  let arguments = (ins OracleSequence:$prefix, OracleHandle:$element,
                       StrArrayAttr:$roles, StrAttr:$site);
  let results = (outs OracleSequence:$output);
  let hasVerifier = 1;
}

def OracleSequenceAtOp : Op<ProtocolDialect, "oracle_sequence_at",
    [MemoryEffects<[MemRead, MemWrite]>,
     ParentOneOf<["zkc::protocol_ir::MathematicalOp", "zkc::protocol_ir::RepeatOp"]>]> {
  let arguments = (ins OracleSequence:$sequence, UI64:$position,
                       StrArrayAttr:$roles, StrAttr:$site);
  let results = (outs OracleHandle:$handle);
  let hasVerifier = 1;
}

def OracleSequenceLengthOp : Op<ProtocolDialect, "oracle_sequence_length",
    [Pure, ParentOneOf<["zkc::protocol_ir::MathematicalOp", "zkc::protocol_ir::RepeatOp"]>]> {
  let arguments = (ins OracleSequence:$sequence);
  let results = (outs UI64:$length);
}

// A closed query declaration has source handles first, ordinary parameters
// next and the queried position last. Its admissibility predicate reads source
// data and ordinary parameters. Native formation retains, but does not prove it.
def OracleDefinitionOp : Op<ProtocolDialect, "oracle",
    [Symbol, IsolatedFromAbove, SingleBlock,
     HasParent<"zkc::protocol_ir::ProtocolModuleOp">,
     DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins SymbolNameAttr:$sym_name,
    TypeAttrOf<FunctionType>:$function_type, OracleKind:$kind,
    FlatSymbolRefAttr:$admissibility,
    OptionalAttr<UI64Attr>:$shape_argument,
    OptionalAttr<UI64Attr>:$maximum_rows);
  let regions = (region AnyRegion:$body);
  let hasRegionVerifier = 1;
  let extraClassDeclaration = [{
    unsigned getNumSources();
  }];
}

def OracleYieldOp : Op<ProtocolDialect, "oracle_yield",
    [Terminator, HasParent<"zkc::protocol_ir::OracleDefinitionOp">]> {
  let arguments = (ins AnyType:$answer);
}

// Fresh occurrence anchor, even for equal sources and parameters. It is not
// an observed oracle query. Query expansion later follows the runtime anchor.
def OracleVirtualOp : Op<ProtocolDialect, "oracle_virtual",
    [MemoryEffects<[MemRead, MemWrite]>,
     ParentOneOf<["zkc::protocol_ir::MathematicalOp", "zkc::protocol_ir::RepeatOp"]>,
     DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins Variadic<AnyType>:$inputs, FlatSymbolRefAttr:$callee,
                       StrAttr:$holder, StrArrayAttr:$receivers);
  let results = (outs OracleHandle:$handle);
}
#endif
