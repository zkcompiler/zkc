#ifndef ZKC_DIALECT_KERNEL_IR_KERNELOPS_TD
#define ZKC_DIALECT_KERNEL_IR_KERNELOPS_TD

include "zkc/Dialect/Kernel/IR/KernelDialect.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/CallInterfaces.td"

def Kernel_ModuleOp : Op<KernelDialect, "module",
    [Symbol, SymbolTable, IsolatedFromAbove, SingleBlock, NoTerminator]> {
  let summary = "closed logical numerical compilation unit";
  let description = [{
    Owns exactly one public standard func.func entry, private standard function
    helpers and private data.domain dependencies. The existing mathematical
    vocabulary defines the body; no participant actions or runtime resources
    enter this boundary. The parent profile owns phase legality.
  }];
  let arguments = (ins SymbolNameAttr:$sym_name);
  let regions = (region AnyRegion:$body);
  let assemblyFormat = "$sym_name attr-dict-with-keyword $body";
  let hasRegionVerifier = 1;
}

def Kernel_CallOp : Op<KernelDialect, "call",
    [CallOpInterface, DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let summary = "ordered invocation of a logical numerical entry from Local";
  let description = [{
    The exact nested symbol path is @unit::@entry. This invocation is ordered
    within local.func and its structured Local control. It has no purity,
    speculation or runtime frame contract. Physical publication requires its
    checked realization into existing executable operations and Local control.
    Optional policy selects [finiteBulk, vectorReductionFusion, collectFoldFusion] at compile time.
  }];
  let arguments = (ins Variadic<AnyType>:$inputs,
    SymbolRefAttr:$callee, StrAttr:$site,
    OptionalAttr<ArrayAttr>:$policy,
    OptionalAttr<DictArrayAttr>:$arg_attrs,
    OptionalAttr<DictArrayAttr>:$res_attrs);
  let results = (outs Variadic<AnyType>:$outputs);
  let extraClassDeclaration = [{
    operand_range getArgOperands() { return getInputs(); }
    ::mlir::MutableOperandRange getArgOperandsMutable() { return getInputsMutable(); }
    ::mlir::CallInterfaceCallable getCallableForCallee() { return getCalleeAttr(); }
    void setCalleeFromCallable(::mlir::CallInterfaceCallable callee) {
      setCalleeAttr(::llvm::cast<::mlir::SymbolRefAttr>(callee));
    }
  }];
  let assemblyFormat = "$callee `(` $inputs `)` attr-dict `:` functional-type($inputs, $outputs)";
  let hasVerifier = 1;
}

#endif
