#ifndef ZKC_DIALECT_ORACLE_IR_ORACLEOPS_TD
#define ZKC_DIALECT_ORACLE_IR_ORACLEOPS_TD

include "zkc/Dialect/Types.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "zkc/Dialect/BoundOperations.td"

def OracleCheckOp : BoundOp<OracleDialect, "exec.check", [OpOracleCheck]>;

def OracleCommitOp : BoundOp<OracleDialect, "exec.commit", [OpOracleCommit]>;

def CommitmentsAppendOp : BoundOp<OracleDialect, "exec.commitments_append", [OpCommitmentsAppend]>;

def CommitmentsAtOp : BoundOp<OracleDialect, "exec.commitments_at", [OpCommitmentsAt]>;

def CommitmentsEmptyOp : BoundOp<OracleDialect, "exec.commitments_empty", [OpCommitmentsEmpty]>;

def CommitmentsLengthOp : BoundOp<OracleDialect, "exec.commitments_length", [OpCommitmentsLength]>;

def OracleOpenOp : BoundOp<OracleDialect, "exec.open", [OpOracleOpen]>;

def OracleOpenManyOp : BoundOp<OracleDialect, "exec.open_many", [OpOracleOpenMany]>;

def OracleCheckManyOp : BoundOp<OracleDialect, "exec.check_many", [OpOracleCheckMany]>;

def OpeningStatesAppendOp : BoundOp<OracleDialect, "exec.opening_states_append", [OpOpeningStatesAppend]>;

def OpeningStatesAtOp : BoundOp<OracleDialect, "exec.opening_states_at", [OpOpeningStatesAt]>;

def OpeningStatesEmptyOp : BoundOp<OracleDialect, "exec.opening_states_empty", [OpOpeningStatesEmpty]>;

def OpeningStatesLengthOp : BoundOp<OracleDialect, "exec.opening_states_length", [OpOpeningStatesLength]>;

#endif
