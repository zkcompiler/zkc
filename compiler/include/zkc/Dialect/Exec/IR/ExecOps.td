#ifndef ZKC_DIALECT_EXEC_IR_EXECOPS_TD
#define ZKC_DIALECT_EXEC_IR_EXECOPS_TD
include "zkc/Dialect/Exec/IR/ExecTypes.td"
include "zkc/Dialect/Runtime/IR/RuntimeTypes.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/IR/SymbolInterfaces.td"
// Logical mathematical invocation. The callee has plain mathematical ports;
// scope borrowing and returned/stopped outcomes belong to this ordered boundary.
// Whole-closure admission and actual candidate checking belong to its consumer.
def Exec_ComputeOp : Op<ExecDialect, "compute",
    [DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins RuntimeScope:$scope, Variadic<AnyType>:$inputs,
    SymbolRefAttr:$callee, StrAttr:$site, OptionalAttr<ArrayAttr>:$policy);
  let results = (outs ExecOutcome:$outcome);
  let hasVerifier = 1;
  let extraClassDeclaration = [{
    // Formation-only resolution of the actual source helper or selected entry.
    // This does not establish mathematical closure or source correspondence.
    ::mlir::func::FuncOp resolveCallee(::mlir::SymbolTableCollection &symbols);
  }];
}
// Ordered finite requests retain actual domain and callback associations until
// selection. They have no loop region and are not ordinary callback ABI calls.
class ExecFinite<string name, string helper> : Op<ExecDialect, name,
    [DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = !if(!eq(helper, "step"),
    (ins RuntimeScope:$scope, Variadic<AnyType>:$inputs,
      FlatSymbolRefAttr:$domain, FlatSymbolRefAttr:$step,
      OptionalAttr<FlatSymbolRefAttr>:$predicate, StrAttr:$site),
    (ins RuntimeScope:$scope, Variadic<AnyType>:$inputs,
      FlatSymbolRefAttr:$domain, FlatSymbolRefAttr:$body,
      OptionalAttr<FlatSymbolRefAttr>:$predicate, StrAttr:$site));
  let results = (outs ExecOutcome:$outcome);
  let hasVerifier = 1;
}
def Exec_FoldOp : ExecFinite<"fold", "step">;
def Exec_CollectOp : ExecFinite<"collect", "body">;
// A reached native instruction uses the active scope. Its outcome includes
// tick, admission, allocation and output binding, not merely its value result.
def Exec_ApplyOp : Op<ExecDialect, "apply"> {
  let arguments = (ins RuntimeScope:$scope, Variadic<AnyType>:$inputs,
    FlatSymbolRefAttr:$binding, StrArrayAttr:$parameters, StrAttr:$site);
  let results = (outs ExecOutcome:$outcome);
  let hasVerifier = 1;
}
def Exec_CompleteOp : Op<ExecDialect, "complete"> {
  let arguments = (ins RuntimeScope:$scope, Variadic<AnyType>:$values);
  let results = (outs ExecOutcome:$outcome);
  let hasVerifier = 1;
}
def Exec_BooleanOp : Op<ExecDialect, "boolean"> {
  let arguments = (ins RuntimeScope:$scope, BoolAttr:$value, StrAttr:$site);
  let results = (outs ExecOutcome:$outcome);
  let hasVerifier = 1;
}
def Exec_RejectOp : Op<ExecDialect, "reject"> {
  let arguments = (ins RuntimeScope:$scope, StrAttr:$reason, StrAttr:$site);
  let results = (outs ExecStop:$stop);
  let hasVerifier = 1;
}
def Exec_TestOp : Op<ExecDialect, "test"> {
  let arguments = (ins RuntimeScope:$scope, AnyType:$condition, StrAttr:$site);
  let results = (outs ExecOutcome:$outcome);
  let hasVerifier = 1;
}
def Exec_RangeOp : Op<ExecDialect, "range"> {
  let arguments = (ins RuntimeScope:$scope, AnyType:$lower, AnyType:$upper,
    StrAttr:$site);
  let results = (outs ExecOutcome:$outcome);
  let hasVerifier = 1;
}
def Exec_VariantOp : Op<ExecDialect, "variant"> {
  let arguments = (ins RuntimeScope:$scope, Variadic<AnyType>:$payload,
    StrAttr:$alternative, StrAttr:$site);
  let results = (outs ExecOutcome:$outcome);
  let hasVerifier = 1;
}
def Exec_MatchOp : Op<ExecDialect, "match", [Terminator,
    DeclareOpInterfaceMethods<BranchOpInterface>]> {
  let arguments = (ins RuntimeScope:$scope, AnyType:$input,
    Variadic<AnyType>:$captures, StrArrayAttr:$alternatives, StrAttr:$site);
  let successors = (successor AnySuccessor:$stopped,
                              VariadicSuccessor<AnySuccessor>:$arms);
  let hasVerifier = 1;
}
// These boundaries are ordered and reached. No Pure/speculation annotation:
// admission, call observations and the first stop are semantically visible.
class ExecInvocation<string name, dag attributes = (ins)> : Op<ExecDialect, name> {
  let arguments = !con((ins Variadic<AnyType>:$inputs), attributes);
  let results = (outs ExecOutcome:$outcome);
  let hasVerifier = 1;
}
def Exec_NumericOp : ExecInvocation<"numeric", (ins StrAttr:$calculation)>;
def Exec_InvokeOp : ExecInvocation<"invoke", (ins StrAttr:$deployment)>;
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
