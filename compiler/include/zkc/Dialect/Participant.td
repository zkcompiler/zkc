#ifndef ZKC_DIALECT_PARTICIPANT_TD
#define ZKC_DIALECT_PARTICIPANT_TD
// Independently callable role programs and transport actions.
def ParticipantOp : Op<PIRDialect, "participant", [Symbol, IsolatedFromAbove, SingleBlock,
    DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins SymbolNameAttr:$sym_name, TypeAttrOf<FunctionType>:$function_type,
    StrAttr:$instance, StrAttr:$role, ArrayAttr:$parameters,
    OptionalAttr<ArrayAttr>:$argument_names);
  let regions = (region AnyRegion:$body);
  let hasRegionVerifier = 1;
}
def ParticipantCallOp : Op<PIRDialect, "participant_call",
    [ParentOneOf<["ParticipantOp", "ProtocolLoopOp"]>,
     DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins Variadic<AnyType>:$inputs, StrAttr:$site,
    FlatSymbolRefAttr:$callee);
  let results = (outs Variadic<AnyType>:$outputs);
}
def EmitOp : Op<PIRDialect, "emit",
    [ParentOneOf<["ParticipantOp", "ProtocolLoopOp"]>]> {
  let arguments = (ins AnyType:$input, StrAttr:$site, StrAttr:$schema, StrAttr:$peer);
}
def AwaitOp : Op<PIRDialect, "await",
    [ParentOneOf<["ParticipantOp", "ProtocolLoopOp"]>]> {
  let arguments = (ins StrAttr:$site, StrAttr:$schema, StrAttr:$peer);
  let results = (outs AnyType:$output);
}
def IncompleteOp : Op<PIRDialect, "incomplete",
    [Terminator, ParentOneOf<["ParticipantOp", "ProtocolLoopOp"]>]> {
  let arguments = (ins StrAttr:$site);
}

#endif
