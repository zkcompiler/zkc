#ifndef ZKC_DIALECT_CLAIM_IR_CLAIMOPS_TD
#define ZKC_DIALECT_CLAIM_IR_CLAIMOPS_TD

include "zkc/Dialect/Types.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "zkc/Dialect/Kernels.td"

def ClaimApplyOp : Op<ClaimDialect, "apply"> {
  let arguments = (ins Variadic<ClaimEvidence>:$premises, FlatSymbolRefAttr:$rule);
  let results = (outs ClaimEvidence:$evidence);
}

def ClaimBindingOp : Op<ClaimDialect, "binding"> {
  let arguments = (ins StrAttr:$id, StrAttr:$origin, StrAttr:$name);
  let results = (outs AnyType:$value);
}

def ClaimFinishOp : Op<ClaimDialect, "finish"> {
  let arguments = (ins Variadic<ClaimEvidence>:$requirements);
}

def ClaimInvocationOp : Op<ClaimDialect, "invocation"> {
  let arguments = (ins Variadic<AnyType>:$values, StrAttr:$path,
    StrAttr:$callee, StrAttr:$instance, I64Attr:$input_count);
}

def ClaimKindOp : Op<ClaimDialect, "kind", [Symbol]> {
  let arguments = (ins SymbolNameAttr:$sym_name, ArrayAttr:$types, StrAttr:$meaning);
}

def ClaimLawOp : Op<ClaimDialect, "law", [Symbol]> {
  let arguments = (ins SymbolNameAttr:$sym_name, StrAttr:$premise);
}

def ClaimLoopOp : Op<ClaimDialect, "loop"> {
  let arguments = (ins StrAttr:$path, I64Attr:$count);
}

def ClaimPendingOp : Op<ClaimDialect, "pending"> {
  let arguments = (ins Variadic<AnyType>:$values, FlatSymbolRefAttr:$kind, StrAttr:$id);
  let results = (outs ClaimPending:$pending);
}

def ClaimRequireOp : Op<ClaimDialect, "require"> {
  let arguments = (ins ClaimPending:$pending);
}

def ClaimRuleOp : Op<ClaimDialect, "rule", [Symbol]> {
  let arguments = (ins Variadic<AnyType>:$bindings, SymbolNameAttr:$sym_name,
    FlatSymbolRefAttr:$law, StrAttr:$invocation, StrAttr:$callee,
    I64Attr:$input_count, I64Attr:$output_count, ArrayAttr:$guards,
    ArrayAttr:$premises, StrAttr:$conclusion);
}

def ClaimTerminalOp : Op<ClaimDialect, "terminal"> {
  let arguments = (ins ClaimPending:$pending, I1:$condition, StrAttr:$guard);
  let results = (outs ClaimEvidence:$evidence);
}

#endif
