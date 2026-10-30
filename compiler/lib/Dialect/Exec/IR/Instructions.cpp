#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/TypeFormation.h"

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
      if (failed(verifyValueType(
              [&] {
                auto diagnostic = emitError(UnknownLoc::get(type.getContext()));
                diagnostic.abandon();
                return diagnostic;
              },
              type)))
        return false;
    }
  return true;
}
bool kind(Type type, StringRef expected) {
  if (!admitted({type}, {}))
    return false;
  auto logical = logicalValueType(type);
  auto interface = dyn_cast<CatalogTypeInterface>(logical);
  auto application =
      interface ? interface.getCatalogApplication() : std::nullopt;
  return application && application->constructor == expected;
}

} // namespace
LogicalResult ApplyOp::verifySymbolUses(SymbolTableCollection &symbols) {
  auto *table = SymbolTable::getNearestSymbolTable(*this);
  auto declaration = table
                         ? dyn_cast_or_null<runtime::BindingOp>(
                               symbols.lookupSymbolIn(table, getBindingAttr()))
                         : runtime::BindingOp();
  if (!declaration || !declaration.getContractAttr() ||
      !declaration.getArgumentsAttr())
    return diagnostics::emit(emitOpError(), "binding-reference");
  auto checked = readNativeBinding([&] { return emitOpError(); }, declaration);
  if (failed(checked))
    return failure();
  auto type = executableBindingSignature(checked->valueType);
  if (getOperandTypes() != TypeRange(type.getInputs()) ||
      getOperation()->getResultTypes() != TypeRange(type.getResults()))
    return diagnostics::emit(
        emitOpError(), "binding-signature",
        "invocation differs from its callable executable ABI");
  return verifyInvocationParameters(
      [&] { return emitOpError(); }, declaration.getContract(),
      declaration.getArgumentsAttr(), getParametersAttr());
}
LogicalResult ApplyOp::verify() {
  if (getSite().empty() ||
      !admitted(getInputs().getTypes(), getOutcome().getType().getPayload()))
    return refuse(*this,
                  "ordered invocation requires one admitted value stage");
  // Stage admission, installation and reached parameters remain independent.
  return verifyCallAttributes(*this, getNumOperands(),
                              getOperation()->getNumResults());
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
  Type logical = getInput().getType();
  if (auto represented = dyn_cast<runtime::RepresentedType>(logical))
    logical = represented.getLogical();
  auto variant = dyn_cast<data::VariantType>(logical);
  if (getSite().empty() || !variant ||
      getArms().size() != variant.getAlternatives().size() ||
      getAlternatives().size() != getArms().size() ||
      getForwarded().size() != getArms().size() + 1 ||
      !admitted({getInput().getType()}, {}))
    return refuse(*this, "variant dispatch alternatives or failure edge");
  SmallVector<Type> stopped{StopType::get(getContext())};
  llvm::append_range(stopped, getForwarded()[0].getTypes());
  if (getStopped()->getArgumentTypes() != TypeRange(stopped))
    return refuse(*this,
                  "variant failure edge must bind stop and forwarded values");
  for (auto [i, arm] : llvm::enumerate(variant.getAlternatives())) {
    if (cast<StringAttr>(getAlternatives()[i]).getValue() !=
        arm.getLabel().getValue())
      return refuse(*this, "variant dispatch must preserve declaration order");
    auto types = data::variantPayloadTypes(getInput().getType(),
                                           arm.getLabel().getValue());
    if (!types) {
      llvm::consumeError(types.takeError());
      return refuse(*this, "variant dispatch payload types");
    }
    llvm::append_range(*types, getForwarded()[i + 1].getTypes());
    if (getArms()[i]->getArgumentTypes() != TypeRange(*types))
      return refuse(*this,
                    "variant dispatch must expose exact payload and captures");
  }
  return success();
}
SuccessorOperands MatchOp::getSuccessorOperands(unsigned index) {
  if (index >= getForwarded().size())
    return SuccessorOperands(MutableOperandRange(*this, getNumOperands(), 0));
  if (index == 0)
    return SuccessorOperands(1, getForwardedMutable()[index]);
  auto variant =
      dyn_cast<data::VariantType>(logicalValueType(getInput().getType()));
  unsigned produced =
      variant && index <= variant.getAlternatives().size()
          ? variant.getAlternatives()[index - 1].getPayload().size()
          : 0;
  return SuccessorOperands(produced, getForwardedMutable()[index]);
}
} // namespace zkc::exec
