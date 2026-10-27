#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"

using namespace mlir;
namespace zkc::runtime {
namespace {
LogicalResult refuse(Operation *op, StringRef reason) {
  return diagnostics::emit(op->emitOpError(), "execution-formation", reason);
}
bool valueType(Type type) {
  auto bound = protocol::encodeBoundType(type, isa<RepresentedType>(type));
  if (!bound) {
    llvm::consumeError(bound.takeError());
    return false;
  }
  return true;
}
bool payloadTypes(TypeRange types) {
  std::optional<bool> represented;
  for (Type type : types) {
    if (!type)
      return false;
    bool physical = isa<RepresentedType>(type);
    if (!valueType(type) || (represented && *represented != physical))
      return false;
    represented = physical;
  }
  return true;
}
bool transferOutcome(exec::OutcomeType outcome, TypeRange payload) {
  if (outcome.getPayload().size() != 1)
    return false;
  auto transfer = dyn_cast<TransferType>(outcome.getPayload().front());
  return transfer && TypeRange(transfer.getPayload()) == payload;
}
} // namespace

LogicalResult
TransferType::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                     ArrayRef<Type> payload) {
  if (!payloadTypes(payload))
    return diagnostics::emit(
        emit(), "execution-formation",
        "transfer payload must use one stage of admitted value types");
  return success();
}

LogicalResult EnterScopeOp::verify() {
  auto payload = getOutcome().getType().getPayload();
  if (payload.size() != 1 || !isa<ScopeType>(payload.front()) ||
      getSite().empty() || !payloadTypes(getInputs().getTypes()))
    return refuse(*this, "scope entry ports or occurrence");
  auto kind = getKind();
  bool coordinate = bool(getCoordinate());
  bool callee = bool(getCalleeAttr());
  auto selection = getSelectionAttr();
  if (kind == "function") {
    if (coordinate || !callee || selection)
      return refuse(*this, "function scope requires only its actual callee");
  } else if (kind == "conditional") {
    if (coordinate || callee || !selection ||
        (selection.getValue() != "then" && selection.getValue() != "else"))
      return refuse(*this, "conditional scope requires its selected branch");
  } else if (kind == "iteration") {
    if (!coordinate || callee || selection)
      return refuse(*this, "iteration scope requires its actual coordinate");
  } else if (kind == "match") {
    if (coordinate || callee || !selection || selection.getValue().empty())
      return refuse(*this, "match scope requires its selected alternative");
  } else {
    return refuse(*this, "unknown execution scope kind");
  }
  return success();
}
LogicalResult ExitScopeOp::verify() {
  auto payload = getBody().getType().getPayload();
  if (!payloadTypes(payload) ||
      !transferOutcome(getOutcome().getType(), payload))
    return refuse(*this, "scope exit must hold the exact body payload");
  return success();
}
LogicalResult BorrowTransferOp::verify() {
  if (getInputs().getTypes() != TypeRange(getTransfer().getType().getPayload()))
    return refuse(*this,
                  "initial transfer payload differs from borrowed values");
  return success();
}
LogicalResult TransferValuesOp::verify() {
  if (getValues().getTypes() != TypeRange(getTransfer().getType().getPayload()))
    return refuse(*this, "borrowed values differ from live transfer payload");
  return success();
}
LogicalResult AcceptTransferOp::verify() {
  if (getOutcome().getType().getPayload() !=
      getTransfer().getType().getPayload())
    return refuse(*this,
                  "parent handoff must retain the exact transfer payload");
  return success();
}
LogicalResult TakeConditionOp::verify() {
  auto payload = getTransfer().getType().getPayload();
  if (payload.empty())
    return refuse(*this, "conditional transfer lacks its Boolean");
  auto condition = protocol::encodeBoundType(
      payload.front(), isa<RepresentedType>(payload.front()));
  if (!condition) {
    llvm::consumeError(condition.takeError());
    return refuse(*this, "conditional transfer has an invalid Boolean");
  }
  if (condition->kind != "bool")
    return refuse(*this, "conditional transfer must start with a Boolean");
  auto returned = getOutcome().getType().getPayload();
  if (returned.size() != 2 || !returned.front().isInteger(1))
    return refuse(*this, "conditional transfer returns a decision and carry");
  auto carry = dyn_cast<TransferType>(returned.back());
  if (!carry || carry.getPayload() != payload.drop_front())
    return refuse(*this, "conditional transfer must preserve the exact carry");
  return success();
}
LogicalResult IterationOp::verify() {
  auto payload = getOutcome().getType().getPayload();
  if (getSite().empty() || payload.size() != 1 || !payloadTypes(payload))
    return refuse(*this, "iteration requires its native index result");
  auto bound = protocol::encodeBoundType(payload.front(),
                                         isa<RepresentedType>(payload.front()));
  if (!bound) {
    llvm::consumeError(bound.takeError());
    return refuse(*this, "iteration index type");
  }
  if (bound->kind != "index")
    return refuse(*this, "iteration requires its native index result");
  return success();
}
LogicalResult ReleaseBindingsOp::verify() {
  if (!payloadTypes(getValues().getTypes()))
    return refuse(*this, "storage release requires admitted value bindings");
  // The executable reader also rejects affine values and later reads. This
  // operation cannot independently establish last use or external uniqueness.
  return success();
}
} // namespace zkc::runtime
