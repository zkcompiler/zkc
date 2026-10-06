#ifndef ZKC_DIALECT_PLAN_IR_PLANTYPES_TD
#define ZKC_DIALECT_PLAN_IR_PLANTYPES_TD

include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/Plan/IR/PlanDialect.td"

def PhysicalData : TypeDef<PlanDialect, "Data"> {
  let mnemonic = "data";
  let parameters = (ins TypeParameter<"::mlir::Type", "Logical type">:$logical,
    StringRefParameter<"Installed representation">:$representation);
  let assemblyFormat = "`<` $logical `,` $representation `>`";
}

#endif
