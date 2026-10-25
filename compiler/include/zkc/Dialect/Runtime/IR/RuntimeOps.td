#ifndef ZKC_DIALECT_RUNTIME_IR_RUNTIMEOPS_TD
#define ZKC_DIALECT_RUNTIME_IR_RUNTIMEOPS_TD
include "zkc/Dialect/Runtime/IR/RuntimeTypes.td"
include "zkc/Dialect/Exec/IR/ExecTypes.td"
include "zkc/Dialect/BoundOperations.td"
// Scope transitions and handoffs are ordered, non-speculatable operations.
// Shape verification is separate from actual-CFG/profile admission and does
// not supply a second native evaluator or an independent resource ledger.
def Runtime_EnterScopeOp : Op<RuntimeDialect, "enter_scope",
    [AttrSizedOperandSegments]> {
  let arguments = (ins RuntimeScope:$parent, Optional<I64>:$coordinate,
    Variadic<AnyType>:$inputs, StrAttr:$kind, StrAttr:$site,
    OptionalAttr<FlatSymbolRefAttr>:$callee, OptionalAttr<StrAttr>:$selection);
  let results = (outs ExecOutcome:$outcome);
  let hasVerifier = 1;
}
def Runtime_ExitScopeOp : Op<RuntimeDialect, "exit_scope"> {
  let description = [{
    Consume an acquired scope and its explicit body outcome. On return, pin
    backing, close body bindings and leave the backend frame in that order.
    A failed leave releases the hold and withholds the successful payload.
    On stop, close bindings and append failed cleanup to the existing cause.
    The successful result is a transfer; publication into the parent is separate.
  }];
  let arguments = (ins RuntimeScope:$scope, ExecOutcome:$body);
  let results = (outs ExecOutcome:$outcome);
  let hasVerifier = 1;
}
def Runtime_BorrowTransferOp : Op<RuntimeDialect, "borrow_transfer"> {
  let arguments = (ins RuntimeScope:$parent, Variadic<AnyType>:$inputs);
  let results = (outs RuntimeTransfer:$transfer);
  let hasVerifier = 1;
}
def Runtime_TransferValuesOp : Op<RuntimeDialect, "transfer_values"> {
  let arguments = (ins RuntimeTransfer:$transfer);
  let results = (outs Variadic<AnyType>:$values);
  let hasVerifier = 1;
}
def Runtime_AcceptTransferOp : Op<RuntimeDialect, "accept_transfer"> {
  let arguments = (ins RuntimeScope:$parent, RuntimeTransfer:$transfer);
  let results = (outs ExecOutcome:$outcome);
  let hasVerifier = 1;
}
def Runtime_ReleaseTransferOp : Op<RuntimeDialect, "release_transfer"> {
  let arguments = (ins RuntimeTransfer:$transfer);
}
def Runtime_TakeConditionOp : Op<RuntimeDialect, "take_condition"> {
  let arguments = (ins RuntimeTransfer:$transfer);
  let results = (outs ExecOutcome:$outcome);
  let hasVerifier = 1;
}
def PrepareQuotientMatrixOp : BoundOp<RuntimeDialect, "prepare_quotient_matrix", [OpQuotientPrepareMatrix]>;
def QuotientMatvecOp : BoundOp<RuntimeDialect, "quotient_matvec", [OpQuotientMatvec]>;
#endif
