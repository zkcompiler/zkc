#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "llvm/ADT/TypeSwitch.h"
#include "llvm/Support/JSON.h"
using namespace mlir;
#include "zkc/Dialect/Exec/IR/execDialect.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Exec/IR/execTypes.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Exec/IR/execOps.cpp.inc"
void zkc::exec::ExecDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Exec/IR/execTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Exec/IR/execOps.cpp.inc"
      >();
}
namespace zkc::exec {
namespace {
LogicalResult refuse(Operation *op, StringRef reason) {
  return diagnostics::emit(op->emitOpError(), "execution-formation", reason);
}
LogicalResult descriptor(Operation *op, StringRef expected,
                         StringRef key = {}) {
  auto attr = op->getAttrOfType<StringAttr>("descriptor");
  auto parsed = llvm::json::parse(attr.getValue());
  if (!parsed) {
    llvm::consumeError(parsed.takeError());
    return refuse(op, "invalid invocation descriptor");
  }
  auto *object = parsed->getAsObject();
  if (!object || object->getString("op") != expected ||
      object->size() != (key.empty() ? 1 : 2) ||
      (!key.empty() &&
       (!object->getString(key) || object->getString(key)->empty())))
    return refuse(op, "invocation descriptor identity");
  return success();
}
} // namespace
LogicalResult NumericOp::verify() {
  return descriptor(*this, "numeric", "calculation");
}
LogicalResult InvokeOp::verify() {
  if (getOutcome().getType().getPayload().size() != 1)
    return refuse(*this, "invocation requires one logical result");
  return descriptor(*this, "invoke", "deployment");
}
LogicalResult RequireOp::verify() {
  if (getInputs().size() != 1 || !getInputs()[0].getType().isInteger(1) ||
      !getOutcome().getType().getPayload().empty())
    return refuse(*this, "require takes one Boolean and returns no values");
  return descriptor(*this, "require");
}
LogicalResult DropOp::verify() {
  if (getInputs().size() != 1 || !getOutcome().getType().getPayload().empty())
    return refuse(*this, "drop takes one value and returns no values");
  return descriptor(*this, "drop");
}
LogicalResult ReturnOp::verify() {
  if (getValues().getTypes() != TypeRange(getOutcome().getType().getPayload()))
    return refuse(*this, "returned payload types differ from outcome");
  return success();
}
LogicalResult DispatchOp::verify() {
  if (getReturned() == getStopped() ||
      getReturned()->getArgumentTypes() !=
          TypeRange(getOutcome().getType().getPayload()) ||
      getStopped()->getNumArguments() != 1 ||
      !isa<StopType>(getStopped()->getArgument(0).getType()))
    return refuse(*this,
                  "outcome edges must bind returned payload or terminal stop");
  return success();
}
SuccessorOperands DispatchOp::getSuccessorOperands(unsigned index) {
  return SuccessorOperands(
      index == 0 ? getOutcome().getType().getPayload().size() : 1,
      MutableOperandRange(*this, 0, 0));
}
} // namespace zkc::exec
