#ifndef ZKC_DIALECT_PROTOCOL_TD
#define ZKC_DIALECT_PROTOCOL_TD
// Common declarations, interaction and shared structured control.
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
def ProtocolModuleOp : Op<PIRDialect, "module",
    [IsolatedFromAbove, SymbolTable, SingleBlock, NoTerminator]> {
  let arguments = (ins StrAttr:$stage);
  let regions = (region AnyRegion:$body);
  let hasRegionVerifier = 1;
}
// Closed operation applications. Logical contracts and physical selections are
// checked against installed declarations; these symbols cannot invent kernels.
def OperationBindingOp : Op<PIRDialect, "operation_binding", [Symbol, HasParent<"ProtocolModuleOp">]> {
  let arguments = (ins SymbolNameAttr:$sym_name, StrAttr:$contract,
    ArrayAttr:$arguments, StrAttr:$implementation);
  let hasVerifier = 1;
}
class CallableProtocolOp<string name> : Op<PIRDialect, name,
    [Symbol, IsolatedFromAbove,
     DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins SymbolNameAttr:$sym_name, TypeAttrOf<FunctionType>:$function_type,
    ArrayAttr:$input_roles, ArrayAttr:$output_roles, ArrayAttr:$roles,
    ArrayAttr:$parameters, ArrayAttr:$dependencies, BoolAttr:$external,
    OptionalAttr<ArrayAttr>:$argument_names);
  let regions = (region AnyRegion:$body);
  let hasRegionVerifier = 1;
}
def ProtocolOp : CallableProtocolOp<"protocol">;
def InstanceOp : Op<PIRDialect, "instance", [Symbol, DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins SymbolNameAttr:$sym_name, FlatSymbolRefAttr:$protocol,
    ArrayAttr:$parameters, ArrayAttr:$dependencies, ArrayAttr:$roles);
}
def ProtocolEntryOp : Op<PIRDialect, "entry", [Symbol, HasParent<"ProtocolModuleOp">, DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins SymbolNameAttr:$sym_name, ArrayAttr:$targets);
}
def LocalCallOp : Op<PIRDialect, "local_call",
    [ParentOneOf<["ProtocolOp", "ParticipantOp", "ProtocolLoopOp"]>,
     DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins Variadic<AnyType>:$inputs, FlatSymbolRefAttr:$callee,
    StrAttr:$site, OptionalAttr<StrAttr>:$role);
  let results = (outs Variadic<AnyType>:$outputs);
}
def MessageOp : Op<PIRDialect, "message",
    [SameOperandsAndResultType, ParentOneOf<["ProtocolOp", "ProtocolLoopOp"]>]> {
  let arguments = (ins AnyType:$input, StrAttr:$site, StrAttr:$schema,
    StrAttr:$sender, StrAttr:$receiver);
  let results = (outs AnyType:$output);
}
// dependency is a local alias in the enclosing protocol, not a SymbolRefAttr.
def ProtocolCallOp : Op<PIRDialect, "protocol_call",
    [ParentOneOf<["ProtocolOp", "ParticipantOp", "ProtocolLoopOp"]>,
     DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins Variadic<AnyType>:$inputs, StrAttr:$site, StrAttr:$dependency);
  let results = (outs Variadic<AnyType>:$outputs);
}
def ProtocolLoopOp : Op<PIRDialect, "loop", [IsolatedFromAbove, SingleBlock,
     ParentOneOf<["ProtocolOp", "ParticipantOp", "ProtocolLoopOp"]>]> {
  let arguments = (ins Variadic<AnyType>:$inputs, StrAttr:$site,
    I64Attr:$carried, StrAttr:$count, BoolAttr:$parameter);
  let results = (outs Variadic<AnyType>:$outputs);
  let regions = (region AnyRegion:$body);
  let hasRegionVerifier = 1;
}
def ProtocolYieldOp : Op<PIRDialect, "yield", [Terminator, HasParent<"ProtocolLoopOp">]> {
  let arguments = (ins Variadic<AnyType>:$inputs);
}
def FinishOp : Op<PIRDialect, "finish",
    [Terminator, ParentOneOf<["ProtocolOp", "ParticipantOp"]>]> {
  let arguments = (ins Variadic<AnyType>:$inputs);
}
def HaltOp : Op<PIRDialect, "halt",
    [Terminator, ParentOneOf<["ProtocolOp", "ParticipantOp", "ProtocolLoopOp", "::mlir::func::FuncOp", "LocalIfOp", "LocalForOp", "LocalMatchOp"]>]> {
  let arguments = (ins StrAttr:$site, StrAttr:$reason, OptionalAttr<StrAttr>:$role);
}

// Local controls preserve logical/physical bound types without index casts.
// Explicit block arguments make region scope isolated, including both paths.
class LocalControlOp<string name> : Op<PIRDialect, name,
    [IsolatedFromAbove, SingleBlock,
     DeclareOpInterfaceMethods<RegionBranchOpInterface,
       ["getEntrySuccessorOperands", "getSuccessorInputs"]>]> {
  let arguments = (ins Variadic<AnyType>:$inputs, StrAttr:$site);
  let results = (outs Variadic<AnyType>:$outputs);
  let hasRegionVerifier = 1;
}
def VariantInjectOp : Op<PIRDialect, "variant_inject"> {
  let description = [{
    Builds a local variant value from the payload of one named alternative. Only
    that alternative's payload is stored; no placeholder is created for the
    others, so an affine payload is transferred exactly once
    (docs/spec/profiles/compiler/local-variants.md).
  }];
  let arguments = (ins Variadic<AnyType>:$payload, StrAttr:$site, StrAttr:$alternative);
  let results = (outs AnyType:$output);
  let hasVerifier = 1;
}
def LocalMatchOp : LocalControlOp<"local_match"> {
  let description = [{
    Operand zero is a local variant; the remaining operands are captures. There
    is one isolated region per declared alternative, in declaration order. Only
    the region of the active alternative executes; its arguments are that
    alternative's payload followed by the captures, so the payload is not a
    successor operand of the variant. A terminal stop inside a region bypasses
    every continuation (docs/spec/profiles/compiler/local-variants.md).
  }];
  let arguments = (ins Variadic<AnyType>:$inputs, StrAttr:$site, ArrayAttr:$alternatives);
  let regions = (region VariadicRegion<AnyRegion>:$arms);
}
def LocalIfOp : LocalControlOp<"local_if"> {
  let description = [{
    Operand zero is a logical bool (i1), or its selected physical wrapper.
    Remaining operands are captures, copied to each isolated region's arguments.
    Both regions are verified; only the selected region executes. Its yield
    supplies every result. Affine captures transfer once at entry, independently
    of which branch is selected. This op is intentionally not speculatable.
  }];
  let regions = (region AnyRegion:$thenRegion, AnyRegion:$elseRegion);
}
def LocalForOp : LocalControlOp<"local_for"> {
  let description = [{
    Operands are lower, upper, initial carried values (one per result), then
    non-affine captures. Bounds are bound index values (ui64 or plan.data), not
    host MLIR index values. Evaluate bounds once and iterate [lower, upper) by
    one; inverted or equal bounds yield initial values. Runtime bounds and
    iteration limits apply before entering a body; no unsigned subtraction wraps.

    Body arguments are generated induction, carried values, then captures.
    The local_yield carries the next values followed by the unchanged capture
    arguments. Trailing capture forwarding is checked and removed at source
    export; it makes every invariant's entry/backedge mapping explicit to MLIR.
    The operation has no unrolling, speculation, or purity trait.
  }];
  let regions = (region AnyRegion:$body);
}
def LocalYieldOp : Op<PIRDialect, "local_yield",
    [Terminator, ParentOneOf<["LocalIfOp", "LocalForOp", "LocalMatchOp"]>,
     DeclareOpInterfaceMethods<RegionBranchTerminatorOpInterface,
       ["getMutableSuccessorOperands"]>]> {
  let arguments = (ins Variadic<AnyType>:$inputs);
}
#endif
