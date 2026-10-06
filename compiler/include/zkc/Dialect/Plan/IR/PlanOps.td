#ifndef ZKC_DIALECT_PLAN_IR_PLANOPS_TD
#define ZKC_DIALECT_PLAN_IR_PLANOPS_TD

include "zkc/Dialect/Types.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "zkc/Dialect/Kernels.td"

def ExecuteKernelOp : Op<PlanDialect, "kernel"> {
  let arguments = (ins Variadic<PhysicalData>:$inputs, StrAttr:$site,
    StrAttr:$kernel, ArrayAttr:$parameters,
    OptionalAttr<FlatSymbolRefAttr>:$binding);
  let results = (outs Variadic<PhysicalData>:$outputs);
  let hasVerifier = 1;
}

def Plan_BoolConstantOp : Op<PlanDialect, "bool_constant"> {
  let arguments = (ins BoolAttr:$value, StrAttr:$site);
  let results = (outs PhysicalData:$output);
  let hasVerifier = 1;
}

def ReleaseOp : Op<PlanDialect, "release"> {
  let arguments = (ins Variadic<PhysicalData>:$values);
  let hasVerifier = 1;
}

#endif
