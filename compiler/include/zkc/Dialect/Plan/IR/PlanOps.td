#ifndef ZKC_DIALECT_PLAN_IR_PLANOPS_TD
#define ZKC_DIALECT_PLAN_IR_PLANOPS_TD

include "zkc/Dialect/Types.td"
include "zkc/Dialect/Plan/IR/PlanDialect.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "zkc/Dialect/BoundOperations.td"

def Plan_ApplyOp : Op<PlanDialect, "apply"> {
  let arguments = (ins Variadic<RepresentedValue>:$inputs, StrAttr:$site,
    StrAttr:$implementation, ArrayAttr:$parameters,
    OptionalAttr<FlatSymbolRefAttr>:$binding);
  let results = (outs Variadic<RepresentedValue>:$outputs);
  let hasVerifier = 1;
}

def Plan_BoolConstantOp : Op<PlanDialect, "bool_constant"> {
  let arguments = (ins BoolAttr:$value, StrAttr:$site);
  let results = (outs RepresentedValue:$output);
  let hasVerifier = 1;
}

def ReleaseOp : Op<PlanDialect, "release"> {
  let arguments = (ins Variadic<RepresentedValue>:$values);
  let hasVerifier = 1;
}

#endif
