#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"

using namespace mlir;
namespace zkc::exec {
namespace {
LogicalResult refuse(Operation *op, StringRef reason) {
  return diagnostics::emit(op->emitOpError(), "execution-formation", reason);
}
bool admitted(TypeRange inputs, TypeRange outputs) {
  std::optional<bool> stage;
  for (TypeRange types : {inputs, outputs})
    for (Type type : types) {
      bool represented = isa<runtime::RepresentedType>(type);
      if (stage && *stage != represented)
        return false;
      stage = represented;
      auto bound = protocol::encodeBoundType(type, represented);
      if (!bound) {
        llvm::consumeError(bound.takeError());
        return false;
      }
    }
  return true;
}
bool kind(Type type, StringRef expected) {
  auto bound =
      protocol::encodeBoundType(type, isa<runtime::RepresentedType>(type));
  if (!bound) {
    llvm::consumeError(bound.takeError());
    return false;
  }
  return bound->kind == expected;
}
} // namespace
LogicalResult ApplyOp::verify() {
  if (getSite().empty() ||
      !admitted(getInputs().getTypes(), getOutcome().getType().getPayload()))
    return refuse(*this,
                  "ordered invocation requires one admitted value stage");
  // Binding resolution, exact ports and parameter formation are independently
  // checked by the enclosing profile with its explicit logical/physical stage.
  return success();
}
LogicalResult CompleteOp::verify() {
  if (getValues().getTypes() !=
          TypeRange(getOutcome().getType().getPayload()) ||
      !admitted(getValues().getTypes(), {}))
    return refuse(*this, "completion must return its exact admitted payload");
  return success();
}
LogicalResult BooleanOp::verify() {
  auto payload = getOutcome().getType().getPayload();
  if (getSite().empty() || payload.size() != 1 ||
      !kind(payload.front(), "bool"))
    return refuse(*this, "Boolean instruction requires its Boolean result");
  return success();
}
LogicalResult RejectOp::verify() {
  if (getSite().empty() || getReason().empty())
    return refuse(*this, "rejection requires its occurrence and reason");
  return success();
}
LogicalResult TestOp::verify() {
  auto payload = getOutcome().getType().getPayload();
  if (getSite().empty() || !kind(getCondition().getType(), "bool") ||
      payload.size() != 1 || !payload.front().isSignlessInteger(1))
    return refuse(*this, "conditional admission requires a Boolean decision");
  return success();
}
LogicalResult RangeOp::verify() {
  auto payload = getOutcome().getType().getPayload();
  if (getSite().empty() || getLower().getType() != getUpper().getType() ||
      !kind(getLower().getType(), "index") || payload.size() != 2 ||
      !llvm::all_of(payload, [](Type t) { return t.isSignlessInteger(64); }))
    return refuse(*this, "range admission requires exact bounds and counters");
  return success();
}
LogicalResult VariantOp::verify() {
  auto payload = getOutcome().getType().getPayload();
  if (getSite().empty() || payload.size() != 1)
    return refuse(*this, "variant construction requires one carrier result");
  auto expected = data::variantPayloadTypes(payload.front(), getAlternative());
  if (!expected) {
    llvm::consumeError(expected.takeError());
    return refuse(*this, "variant alternative or carrier");
  }
  if (getPayload().getTypes() != TypeRange(*expected))
    return refuse(*this,
                  "variant payload differs from its declared alternative");
  return success();
}
LogicalResult MatchOp::verify() {
  auto bound = protocol::encodeBoundType(
      getInput().getType(),
      isa<runtime::RepresentedType>(getInput().getType()));
  if (!bound) {
    llvm::consumeError(bound.takeError());
    return refuse(*this, "variant dispatch input type");
  }
  auto descriptor = protocol::decodeVariant("variant:" + bound->identity);
  if (getSite().empty() || bound->kind != "variant" || !descriptor ||
      getArms().size() != descriptor->alternatives.size() ||
      getAlternatives().size() != getArms().size() ||
      getStopped()->getNumArguments() != 1 ||
      !isa<StopType>(getStopped()->getArgument(0).getType()) ||
      !admitted(getCaptures().getTypes(), {getInput().getType()}))
    return refuse(*this, "variant dispatch alternatives or failure edge");
  for (auto [i, arm] : llvm::enumerate(descriptor->alternatives)) {
    if (cast<StringAttr>(getAlternatives()[i]).getValue() != arm.label)
      return refuse(*this, "variant dispatch must preserve declaration order");
    auto types = data::variantPayloadTypes(getInput().getType(), arm.label);
    if (!types) {
      llvm::consumeError(types.takeError());
      return refuse(*this, "variant dispatch payload types");
    }
    llvm::append_range(*types, getCaptures().getTypes());
    if (getArms()[i]->getArgumentTypes() != TypeRange(*types))
      return refuse(*this,
                    "variant dispatch must expose exact payload and captures");
  }
  return success();
}
SuccessorOperands MatchOp::getSuccessorOperands(unsigned index) {
  if (index == 0)
    return SuccessorOperands(1, MutableOperandRange(*this, 0, 0));
  auto count = getArms()[index - 1]->getNumArguments();
  return SuccessorOperands(
      count >= getCaptures().size() ? count - getCaptures().size() : 0,
      getCapturesMutable());
}
} // namespace zkc::exec
