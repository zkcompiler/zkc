#ifndef ZKC_DIALECT_EXEC_IR_EXECOPS_TD
#define ZKC_DIALECT_EXEC_IR_EXECOPS_TD
include "zkc/Dialect/Exec/IR/ExecTypes.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
// These boundaries are ordered and reached. No Pure/speculation annotation:
// admission, call observations and the first stop are semantically visible.
class ExecInvocation<string name> : Op<ExecDialect, name> {
  let arguments = (ins Variadic<AnyType>:$inputs, StrAttr:$descriptor);
  let results = (outs ExecOutcome:$outcome);
  let hasVerifier = 1;
}
def Exec_NumericOp : ExecInvocation<"numeric">;
def Exec_InvokeOp : ExecInvocation<"invoke">;
def Exec_RequireOp : ExecInvocation<"require">;
def Exec_DropOp : ExecInvocation<"drop">;
def Exec_StopOp : Op<ExecDialect, "stop"> {
  let arguments = (ins StrAttr:$reason);
  let results = (outs ExecStop:$stop);
}
def Exec_ReturnOp : Op<ExecDialect, "returned"> {
  let arguments = (ins Variadic<AnyType>:$values);
  let results = (outs ExecOutcome:$outcome);
  let hasVerifier = 1;
}
def Exec_FailureOp : Op<ExecDialect, "failed"> {
  let arguments = (ins ExecStop:$stop);
  let results = (outs ExecOutcome:$outcome);
}
def Exec_DispatchOp : Op<ExecDialect, "dispatch", [Terminator,
    DeclareOpInterfaceMethods<BranchOpInterface>]> {
  let arguments = (ins ExecOutcome:$outcome);
  let successors = (successor AnySuccessor:$returned, AnySuccessor:$stopped);
  let hasVerifier = 1;
}
#endif
