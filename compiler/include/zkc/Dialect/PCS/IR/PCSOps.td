#ifndef ZKC_DIALECT_PCS_IR_PCSOPS_TD
#define ZKC_DIALECT_PCS_IR_PCSOPS_TD

include "zkc/Dialect/Types.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "zkc/Dialect/Kernels.td"

def PCSCheckOp : KernelOp<PCSDialect, "exec.check", [OpPcsCheck]>;

def PCSCommitOp : KernelOp<PCSDialect, "exec.commit", [OpPcsCommit]>;

def PCSEqualOp : KernelOp<PCSDialect, "exec.equal", [OpPcsEqual]>;

def PCSOpenOp : KernelOp<PCSDialect, "exec.open", [OpPcsOpen]>;

#endif
