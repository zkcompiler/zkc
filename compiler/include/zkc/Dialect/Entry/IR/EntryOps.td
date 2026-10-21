#ifndef ZKC_DIALECT_ENTRY_IR_ENTRYOPS_TD
#define ZKC_DIALECT_ENTRY_IR_ENTRYOPS_TD
include "zkc/Dialect/Entry/IR/EntryTypes.td"
class EntryOperation<string name> : Op<EntryDialect, name> {
  let arguments = (ins Variadic<AnyType>:$inputs, StrAttr:$descriptor);
  let results = (outs Variadic<AnyType>:$outputs);
}
def EntryConstructOp : EntryOperation<"construct">;
def EntryUnpackOp : EntryOperation<"unpack">;
// Stop never returns. Typed results close the unreachable structured
// continuation without fabricating data or relaxing SCF terminator checks.
def EntryStopOp : Op<EntryDialect, "stop"> {
  let arguments = (ins StrAttr:$descriptor);
  let results = (outs Variadic<AnyType>:$outputs);
}
def EntryProjectOp : EntryOperation<"project">;
def EntryNumericOp : EntryOperation<"numeric">;
def EntryInvokeOp : EntryOperation<"invoke">;
def EntryRequireOp : EntryOperation<"require">;
def EntryDropOp : EntryOperation<"drop">;
def EntryMatchOp : EntryOperation<"match"> {
  let regions = (region VariadicRegion<AnyRegion>:$arms);
}
def EntryYieldOp : Op<EntryDialect, "yield", [Terminator]> {
  let arguments = (ins Variadic<AnyType>:$inputs);
}
#endif
