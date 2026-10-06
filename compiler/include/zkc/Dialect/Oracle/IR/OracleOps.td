#ifndef ZKC_DIALECT_ORACLE_IR_ORACLEOPS_TD
#define ZKC_DIALECT_ORACLE_IR_ORACLEOPS_TD

include "zkc/Dialect/Types.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "zkc/Dialect/Kernels.td"

def OracleCheckOp : KernelOp<OracleDialect, "exec.check", [OpOracleCheck]>;

def OracleCommitOp : KernelOp<OracleDialect, "exec.commit", [OpOracleCommit]>;

def CommitmentsAppendOp : KernelOp<OracleDialect, "exec.commitments_append", [OpCommitmentsAppend]>;

def CommitmentsAtOp : KernelOp<OracleDialect, "exec.commitments_at", [OpCommitmentsAt]>;

def CommitmentsEmptyOp : KernelOp<OracleDialect, "exec.commitments_empty", [OpCommitmentsEmpty]>;

def CommitmentsLengthOp : KernelOp<OracleDialect, "exec.commitments_length", [OpCommitmentsLength]>;

def OracleOpenOp : KernelOp<OracleDialect, "exec.open", [OpOracleOpen]>;

def OpeningStatesAppendOp : KernelOp<OracleDialect, "exec.opening_states_append", [OpOpeningStatesAppend]>;

def OpeningStatesAtOp : KernelOp<OracleDialect, "exec.opening_states_at", [OpOpeningStatesAt]>;

def OpeningStatesEmptyOp : KernelOp<OracleDialect, "exec.opening_states_empty", [OpOpeningStatesEmpty]>;

def OpeningStatesLengthOp : KernelOp<OracleDialect, "exec.opening_states_length", [OpOpeningStatesLength]>;

#endif
