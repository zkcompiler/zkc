#ifndef ZKC_DIALECT_PROTOCOL_IR_PROTOCOLOPS_TD
#define ZKC_DIALECT_PROTOCOL_IR_PROTOCOLOPS_TD

include "zkc/Dialect/Types.td"
include "zkc/Dialect/Protocol/IR/ProtocolAttrs.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "zkc/Dialect/Kernels.td"

class CallableProtocolOp<string name> : Op<ProtocolDialect, name,
    [Symbol, IsolatedFromAbove,
     DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins SymbolNameAttr:$sym_name, TypeAttrOf<FunctionType>:$function_type,
    ArrayAttr:$input_roles, ArrayAttr:$output_roles, ArrayAttr:$roles,
    ArrayAttr:$parameters, ArrayAttr:$dependencies, BoolAttr:$external,
    OptionalAttr<ArrayAttr>:$argument_names);
  let regions = (region AnyRegion:$body);
  let hasRegionVerifier = 1;
}

def AwaitOp : Op<ProtocolDialect, "receive",
    [ParentOneOf<["zkc::protocol_ir::ParticipantOp", "zkc::protocol_ir::ProtocolLoopOp"]>]> {
  let arguments = (ins StrAttr:$site, StrAttr:$schema, StrAttr:$peer);
  let results = (outs AnyType:$output);
}

def EmitOp : Op<ProtocolDialect, "send",
    [ParentOneOf<["zkc::protocol_ir::ParticipantOp", "zkc::protocol_ir::ProtocolLoopOp"]>]> {
  let arguments = (ins AnyType:$input, StrAttr:$site, StrAttr:$schema, StrAttr:$peer);
}

def ProtocolEntryOp : Op<ProtocolDialect, "entry", [Symbol, HasParent<"zkc::protocol_ir::ProtocolModuleOp">, DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins SymbolNameAttr:$sym_name, ArrayAttr:$targets);
}

// Static protocol composition, expanded before participant projection.
def ApplyOp : Op<ProtocolDialect, "apply",
    [MemoryEffects<[MemRead, MemWrite]>,
     ParentOneOf<["zkc::protocol_ir::MathematicalOp", "zkc::protocol_ir::RepeatOp"]>,
     DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins Variadic<AnyType>:$inputs, FlatSymbolRefAttr:$callee,
    StrArrayAttr:$roles, StrAttr:$site);
  let results = (outs Variadic<AnyType>:$outputs);
  let assemblyFormat = "$callee `(` $inputs `)` attr-dict `:` functional-type($inputs, $outputs)";
}

def ExchangeOp : Op<ProtocolDialect, "exchange",
    [MemoryEffects<[MemRead, MemWrite]>, SameOperandsAndResultType,
     ParentOneOf<["zkc::protocol_ir::MathematicalOp", "zkc::protocol_ir::RepeatOp"]>]> {
  let arguments = (ins AnyType:$input, StrAttr:$site, StrAttr:$sender,
    StrAttr:$receiver);
  let results = (outs AnyType:$output);
  let assemblyFormat = "$input attr-dict `:` type($input)";
}

def FinishOp : Op<ProtocolDialect, "finish",
    [Terminator, HasParent<"zkc::protocol_ir::ParticipantOp">]> {
  let arguments = (ins Variadic<AnyType>:$inputs);
}

// Conditional completion of one entry participant. The false edge returns
// explicit affine SSA successors; the true edge returns the owner's complete
// result tuple. This is an ordered entry action, not a component-local return
// or a retry exception.
def FinishIfOp : Op<ProtocolDialect, "finish_if",
                    [MemoryEffects<[MemRead, MemWrite]>,
                     ParentOneOf<["zkc::protocol_ir::MathematicalOp",
                                  "zkc::protocol_ir::RepeatOp",
                                  "zkc::protocol_ir::ParticipantOp",
                                  "zkc::protocol_ir::ProtocolLoopOp"]>]> {
  let arguments = (ins AnyType:$condition, Variadic<AnyType>:$values,
      StrAttr:$site, StrAttr:$owner);
  let results = (outs Variadic<AnyType>:$continuations);
  let hasVerifier = 1;
}

def GuardOp : Op<ProtocolDialect, "guard",
    [MemoryEffects<[MemRead, MemWrite]>, ParentOneOf<["zkc::protocol_ir::MathematicalOp", "zkc::protocol_ir::RepeatOp"]>]> {
  let arguments = (ins I1:$condition, StrAttr:$site, StrAttr:$owner);
  let assemblyFormat = "$condition attr-dict";
}

def HaltOp : Op<ProtocolDialect, "stop",
    [Terminator, ParentOneOf<["zkc::protocol_ir::ExecFuncOp", "zkc::protocol_ir::ProtocolLoopOp"]>]> {
  let arguments = (ins StrAttr:$site, StrAttr:$reason, StrAttr:$role);
}

def IncompleteOp : Op<ProtocolDialect, "incomplete",
    [Terminator, ParentOneOf<["zkc::protocol_ir::ParticipantOp", "zkc::protocol_ir::ProtocolLoopOp"]>]> {
  let arguments = (ins StrAttr:$site);
}

def InstanceOp : Op<ProtocolDialect, "instance", [Symbol, DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins SymbolNameAttr:$sym_name, FlatSymbolRefAttr:$protocol,
    ArrayAttr:$parameters, ArrayAttr:$dependencies, ArrayAttr:$roles);
}

def LocalCallOp : Op<ProtocolDialect, "local_call",
    [ParentOneOf<["zkc::protocol_ir::ExecFuncOp", "zkc::protocol_ir::MathematicalOp", "zkc::protocol_ir::ProtocolLoopOp", "zkc::protocol_ir::RepeatOp"]>,
     DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins Variadic<AnyType>:$inputs, FlatSymbolRefAttr:$callee,
    StrAttr:$site, StrAttr:$role);
  let results = (outs Variadic<AnyType>:$outputs);
}

// Common iteration is an ordered protocol region, not a pure expression.
// Operand zero is the logical count; then carried values, then captures.
// Body arguments are the induction index, carried values, and captures.
def RepeatOp : Op<ProtocolDialect, "repeat", [IsolatedFromAbove, SingleBlock,
    ParentOneOf<["zkc::protocol_ir::MathematicalOp", "zkc::protocol_ir::RepeatOp"]>]> {
  let arguments = (ins Variadic<AnyType>:$inputs, StrAttr:$site,
    I64Attr:$carried, I64Attr:$maximum, ArrayAttr:$roles,
    ArrayAttr:$carried_roles);
  let results = (outs Variadic<AnyType>:$outputs);
  let regions = (region AnyRegion:$body);
  let hasRegionVerifier = 1;
}

def ProtocolLoopOp : Op<ProtocolDialect, "loop", [IsolatedFromAbove, SingleBlock,
     ParentOneOf<["zkc::protocol_ir::ExecFuncOp", "zkc::protocol_ir::ParticipantOp", "zkc::protocol_ir::ProtocolLoopOp"]>]> {
  let arguments = (ins Variadic<AnyType>:$inputs, StrAttr:$site,
    I64Attr:$carried, StrAttr:$count, BoolAttr:$parameter,
    OptionalAttr<I64Attr>:$maximum);
  let results = (outs Variadic<AnyType>:$outputs);
  let regions = (region AnyRegion:$body);
  let hasRegionVerifier = 1;
}

def MathematicalReturnOp : Op<ProtocolDialect, "return",
    [Terminator, ParentOneOf<["zkc::protocol_ir::MathematicalOp", "zkc::protocol_ir::ExecFuncOp"]>]> {
  let arguments = (ins Variadic<AnyType>:$values);
}

def MathematicalOp : Op<ProtocolDialect, "func",
    [Symbol, IsolatedFromAbove, SingleBlock, HasParent<"zkc::protocol_ir::ProtocolModuleOp">]> {
  let arguments = (ins SymbolNameAttr:$sym_name,
    TypeAttrOf<FunctionType>:$function_type, ArrayAttr:$roles,
    ArrayAttr:$input_roles, ArrayAttr:$output_roles);
  let regions = (region AnyRegion:$body);
  let hasRegionVerifier = 1;
}

def MessageOp : Op<ProtocolDialect, "message",
    [SameOperandsAndResultType, ParentOneOf<["zkc::protocol_ir::ExecFuncOp", "zkc::protocol_ir::ProtocolLoopOp"]>]> {
  let arguments = (ins AnyType:$input, StrAttr:$site, StrAttr:$schema,
    StrAttr:$sender, StrAttr:$receiver);
  let results = (outs AnyType:$output);
}

def ProtocolModuleOp : Op<ProtocolDialect, "module",
    [IsolatedFromAbove, SymbolTable, SingleBlock, NoTerminator]> {
  let arguments = (ins ProtocolProfileAttr:$profile,
    OptionalAttr<ProtocolExecutionContractAttr>:$execution_contract);
  let regions = (region AnyRegion:$body);
  let hasVerifier = 1;
  let hasRegionVerifier = 1;
}

// Retained source interfaces and actual symbol uses. This is compilation
// metadata, not a participant event or a correspondence certificate.
def ProjectionOp : Op<ProtocolDialect, "projection",
    [HasParent<"zkc::protocol_ir::ProtocolModuleOp">, MemoryEffects<[MemWrite]>,
     DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins ArrayAttr:$interfaces, ArrayAttr:$calculations);
}

def ParticipantOp : Op<ProtocolDialect, "participant", [Symbol, IsolatedFromAbove, SingleBlock,
    DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins SymbolNameAttr:$sym_name, TypeAttrOf<FunctionType>:$function_type,
    StrAttr:$instance, StrAttr:$role, ArrayAttr:$parameters,
    OptionalAttr<ArrayAttr>:$argument_names);
  let regions = (region AnyRegion:$body);
  let hasRegionVerifier = 1;
}

def ParticipantCallOp : Op<ProtocolDialect, "participant_call",
    [ParentOneOf<["zkc::protocol_ir::ParticipantOp", "zkc::protocol_ir::ProtocolLoopOp"]>,
     DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins Variadic<AnyType>:$inputs, StrAttr:$site,
    FlatSymbolRefAttr:$callee);
  let results = (outs Variadic<AnyType>:$outputs);
}

def ParticipantQueryOp : Op<ProtocolDialect, "service_query",
    [MemoryEffects<[MemRead, MemWrite]>, ParentOneOf<["zkc::protocol_ir::ParticipantOp", "zkc::protocol_ir::ProtocolLoopOp"]>]> {
  let arguments = (ins Variadic<AnyType>:$inputs, StrAttr:$port, StrAttr:$method, StrAttr:$site);
  let results = (outs Variadic<AnyType>:$outputs);
}

def ExecFuncOp : CallableProtocolOp<"exec_func">;

def ProtocolCallOp : Op<ProtocolDialect, "call",
    [ParentOneOf<["zkc::protocol_ir::ExecFuncOp", "zkc::protocol_ir::ParticipantOp", "zkc::protocol_ir::ProtocolLoopOp"]>,
     DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins Variadic<AnyType>:$inputs, StrAttr:$site, StrAttr:$dependency);
  let results = (outs Variadic<AnyType>:$outputs);
}

def QueryOp : Op<ProtocolDialect, "query",
    [MemoryEffects<[MemRead, MemWrite]>, ParentOneOf<["zkc::protocol_ir::MathematicalOp", "zkc::protocol_ir::RepeatOp"]>]> {
  let arguments = (ins ServiceReference:$reference, Variadic<AnyType>:$inputs,
    StrAttr:$method, StrAttr:$owner, StrAttr:$site);
  let results = (outs Variadic<AnyType>:$outputs);
}

def RestrictRolesOp : Op<ProtocolDialect, "restrict_roles",
    [Pure, SameOperandsAndResultType, ParentOneOf<["zkc::protocol_ir::MathematicalOp", "zkc::protocol_ir::RepeatOp"]>]> {
  let arguments = (ins AnyType:$input, ArrayAttr:$roles);
  let results = (outs AnyType:$output);
  let assemblyFormat = "$input attr-dict `:` type($input)";
}


def StatementOp : Op<ProtocolDialect, "statement",
    [MemoryEffects<[MemWrite]>, HasParent<"zkc::protocol_ir::MathematicalOp">,
     DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins Variadic<AnyType>:$inputs, FlatSymbolRefAttr:$relation,
    ArrayAttr:$selectors, I64Attr:$acceptance);
  let assemblyFormat = "$relation `(` $inputs `)` attr-dict (`:` type($inputs)^)?";
}

def ProtocolYieldOp : Op<ProtocolDialect, "yield", [Terminator, ParentOneOf<["zkc::protocol_ir::ProtocolLoopOp", "zkc::protocol_ir::RepeatOp"]>]> {
  let arguments = (ins Variadic<AnyType>:$inputs);
}

#endif
