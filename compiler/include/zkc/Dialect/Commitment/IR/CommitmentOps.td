#ifndef ZKC_DIALECT_COMMITMENT_IR_COMMITMENTOPS_TD
#define ZKC_DIALECT_COMMITMENT_IR_COMMITMENTOPS_TD

include "zkc/Dialect/Types.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "zkc/Dialect/BoundOperations.td"

def PolynomialCheckOp : BoundOp<CommitmentDialect, "exec.polynomial_check", [OpPcsCheck]>;

def PolynomialCommitOp : BoundOp<CommitmentDialect, "exec.polynomial_commit", [OpPcsCommit]>;

def PolynomialEqualOp : BoundOp<CommitmentDialect, "exec.polynomial_equal", [OpPcsEqual]>;

def PolynomialOpenOp : BoundOp<CommitmentDialect, "exec.polynomial_open", [OpPcsOpen]>;

def VectorCheckOp : BoundOp<CommitmentDialect, "exec.vector_check", [OpOracleCheck]>;

def VectorCommitOp : BoundOp<CommitmentDialect, "exec.vector_commit", [OpOracleCommit]>;

def CommitmentsAppendOp : BoundOp<CommitmentDialect, "exec.commitments_append", [OpCommitmentsAppend]>;

def CommitmentsAtOp : BoundOp<CommitmentDialect, "exec.commitments_at", [OpCommitmentsAt]>;

def CommitmentsEmptyOp : BoundOp<CommitmentDialect, "exec.commitments_empty", [OpCommitmentsEmpty]>;

def CommitmentsLengthOp : BoundOp<CommitmentDialect, "exec.commitments_length", [OpCommitmentsLength]>;

def VectorOpenOp : BoundOp<CommitmentDialect, "exec.vector_open", [OpOracleOpen]>;

def VectorOpenManyOp : BoundOp<CommitmentDialect, "exec.vector_open_many", [OpOracleOpenMany]>;

def VectorCheckManyOp : BoundOp<CommitmentDialect, "exec.vector_check_many", [OpOracleCheckMany]>;

def OpeningStatesAppendOp : BoundOp<CommitmentDialect, "exec.opening_states_append", [OpOpeningStatesAppend]>;

def OpeningStatesAtOp : BoundOp<CommitmentDialect, "exec.opening_states_at", [OpOpeningStatesAt]>;

def OpeningStatesEmptyOp : BoundOp<CommitmentDialect, "exec.opening_states_empty", [OpOpeningStatesEmpty]>;

def OpeningStatesLengthOp : BoundOp<CommitmentDialect, "exec.opening_states_length", [OpOpeningStatesLength]>;

#endif
