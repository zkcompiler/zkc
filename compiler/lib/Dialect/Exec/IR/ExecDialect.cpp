#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "llvm/ADT/TypeSwitch.h"
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
LogicalResult ExecDialect::verifyOperationAttribute(Operation *op,
                                                    NamedAttribute attribute) {
  if (attribute.getName() != "exec.computation" || !isa<mlir::ModuleOp>(op) ||
      !isa<UnitAttr>(attribute.getValue()) ||
      !op->getAttrOfType<StringAttr>("sym_name"))
    return diagnostics::emit(
        op->emitOpError(), "computation-profile",
        "expected a unit marker on a named builtin.module");
  // This hook runs before child-region invariants. Closed-profile admission is
  // owned by the enclosing stage and must inspect every retained declaration.
  return success();
}
namespace {
LogicalResult refuse(Operation *op, StringRef reason) {
  return diagnostics::emit(op->emitOpError(), "execution-formation", reason);
}
} // namespace
LogicalResult NumericOp::verify() {
  return getCalculation().empty() ? refuse(*this, "empty calculation identity")
                                  : success();
}
LogicalResult InvokeOp::verify() {
  if (getOutcome().getType().getPayload().size() != 1)
    return refuse(*this, "invocation requires one logical result");
  return getDeployment().empty() ? refuse(*this, "empty deployment identity")
                                 : success();
}
LogicalResult RequireOp::verify() {
  if (getInputs().size() != 1 || !getInputs()[0].getType().isInteger(1) ||
      !getOutcome().getType().getPayload().empty())
    return refuse(*this, "require takes one Boolean and returns no values");
  return success();
}
LogicalResult DropOp::verify() {
  if (getInputs().size() != 1 || !getOutcome().getType().getPayload().empty())
    return refuse(*this, "drop takes one value and returns no values");
  return success();
}
LogicalResult ReturnOp::verify() {
  if (getValues().getTypes() != TypeRange(getOutcome().getType().getPayload()))
    return refuse(*this, "returned payload types differ from outcome");
  return success();
}
LogicalResult DispatchOp::verify() {
  if (getForwarded().size() != 2)
    return refuse(*this,
                  "outcome dispatch requires one operand segment per edge");
  SmallVector<Type> returned(getOutcome().getType().getPayload());
  llvm::append_range(returned, getForwarded()[0].getTypes());
  SmallVector<Type> stopped{StopType::get(getContext())};
  llvm::append_range(stopped, getForwarded()[1].getTypes());
  if (getReturned() == getStopped() ||
      getReturned()->getArgumentTypes() != TypeRange(returned) ||
      getStopped()->getArgumentTypes() != TypeRange(stopped))
    return refuse(*this,
                  "outcome edges must bind returned payload or terminal stop");
  return success();
}
SuccessorOperands DispatchOp::getSuccessorOperands(unsigned index) {
  // Interface verification precedes the custom verifier. Keep malformed
  // segment inventories diagnosable without indexing past their storage.
  if (index >= getForwarded().size())
    return SuccessorOperands(MutableOperandRange(*this, getNumOperands(), 0));
  return SuccessorOperands(
      index == 0 ? getOutcome().getType().getPayload().size() : 1,
      getForwardedMutable()[index]);
}
} // namespace zkc::exec
