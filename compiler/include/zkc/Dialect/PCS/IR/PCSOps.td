#ifndef ZKC_DIALECT_PCS_IR_PCSOPS_TD
#define ZKC_DIALECT_PCS_IR_PCSOPS_TD

include "zkc/Dialect/Types.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "zkc/Dialect/BoundOperations.td"

def PCSCheckOp : BoundOp<PCSDialect, "exec.check", [OpPcsCheck]>;

def PCSCommitOp : BoundOp<PCSDialect, "exec.commit", [OpPcsCommit]>;

def PCSEqualOp : BoundOp<PCSDialect, "exec.equal", [OpPcsEqual]>;

def PCSOpenOp : BoundOp<PCSDialect, "exec.open", [OpPcsOpen]>;

#endif
