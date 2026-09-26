#ifndef ZKC_DIALECT_CLAIM_TD
#define ZKC_DIALECT_CLAIM_TD
include "mlir/IR/SymbolInterfaces.td"
include "zkc/Dialect/Base.td"

def ClaimDialect : ZKCDialect {
  let name = "claim";
  let cppNamespace = "::zkc";
  let useDefaultTypePrinterParser = 1;
  let description = [{
    Optional execution-bound analysis, checked relative to independently
    retained source and contracts. These operations never execute protocols.
    A pending proposition is not truth. Evidence is reusable logical data;
    it cannot issue, duplicate or advance runtime resources. Body laws remain
    explicit caller trust premises. No logical erasure removes PIR checks.
  }];
}
def ClaimPending : TypeDef<ClaimDialect, "ClaimPending"> {
  let mnemonic = "pending";
}
def ClaimEvidence : TypeDef<ClaimDialect, "ClaimEvidence"> {
  let mnemonic = "evidence";
}
// No Pure/speculation traits: ordinary optimizer passes must retain the
// independently checkable representation. Full source-relative checking is
// claims::checkIR, not the structural MLIR verifier alone.
def ClaimKindOp : Op<ClaimDialect, "kind", [Symbol]> {
  let arguments = (ins SymbolNameAttr:$sym_name, ArrayAttr:$types, StrAttr:$meaning);
}
def ClaimLawOp : Op<ClaimDialect, "law", [Symbol]> {
  let arguments = (ins SymbolNameAttr:$sym_name, StrAttr:$premise);
}
def ClaimBindingOp : Op<ClaimDialect, "binding"> {
  let arguments = (ins StrAttr:$id, StrAttr:$origin, StrAttr:$name);
  let results = (outs AnyType:$value);
}
def ClaimInvocationOp : Op<ClaimDialect, "invocation"> {
  let arguments = (ins Variadic<AnyType>:$values, StrAttr:$path,
    StrAttr:$callee, StrAttr:$instance, I64Attr:$input_count);
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
def ClaimTerminalOp : Op<ClaimDialect, "terminal"> {
  let arguments = (ins ClaimPending:$pending, I1:$condition, StrAttr:$guard);
  let results = (outs ClaimEvidence:$evidence);
}
def ClaimRuleOp : Op<ClaimDialect, "rule", [Symbol]> {
  let arguments = (ins Variadic<AnyType>:$bindings, SymbolNameAttr:$sym_name,
    FlatSymbolRefAttr:$law, StrAttr:$invocation, StrAttr:$callee,
    I64Attr:$input_count, I64Attr:$output_count, ArrayAttr:$guards,
    ArrayAttr:$premises, StrAttr:$conclusion);
}
def ClaimApplyOp : Op<ClaimDialect, "apply"> {
  let arguments = (ins Variadic<ClaimEvidence>:$premises, FlatSymbolRefAttr:$rule);
  let results = (outs ClaimEvidence:$evidence);
}
def ClaimFinishOp : Op<ClaimDialect, "finish"> {
  let arguments = (ins Variadic<ClaimEvidence>:$requirements);
}
#endif
