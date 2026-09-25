#ifndef ZKC_DIALECT_PHYSICAL_TD
#define ZKC_DIALECT_PHYSICAL_TD
// Selected physical representations and contracted execution.
def PhysicalData : TypeDef<PlanDialect, "Data"> {
  let mnemonic = "data";
  let parameters = (ins TypeParameter<"::mlir::Type", "Logical type">:$logical,
    StringRefParameter<"Installed representation">:$representation);
  let assemblyFormat = "`<` $logical `,` $representation `>`";
}
def ExecuteKernelOp : Op<PlanDialect, "kernel"> {
  let arguments = (ins Variadic<PhysicalData>:$inputs, StrAttr:$site,
    StrAttr:$kernel, ArrayAttr:$parameters,
    OptionalAttr<FlatSymbolRefAttr>:$binding);
  let results = (outs Variadic<PhysicalData>:$outputs);
  let hasVerifier = 1;
}

// Discard ordinary local value storage without changing logical accounting.
// Deliberately has no purity/speculation traits.
def ReleaseOp : Op<PlanDialect, "release"> {
  let arguments = (ins Variadic<PhysicalData>:$values);
  let hasVerifier = 1;
}

#endif
