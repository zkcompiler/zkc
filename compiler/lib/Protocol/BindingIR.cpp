#include "mlir/IR/SymbolTable.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Protocol/Bindings.h"
#include "zkc/Protocol/Kernels.h"
#include "zkc/Protocol/Module.h"
#include "zkc/Target/Json.h"

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {

Expected<source::OperationBinding> readBinding(Operation *op) {
  auto declaration = dyn_cast_or_null<OperationBindingOp>(op);
  if (!declaration || !isa_and_nonnull<ProtocolModuleOp>(op->getParentOp()))
    return error("binding-declaration-context");
  auto name = declaration.getSymNameAttr();
  auto contract = declaration.getContractAttr();
  auto implementation = declaration.getImplementationAttr();
  auto arguments = declaration.getArgumentsAttr();
  if (!name || !contract || !implementation || !arguments)
    return error("binding-declaration");
  source::Names values;
  for (auto arg : arguments) {
    auto value = dyn_cast<StringAttr>(arg);
    if (!value)
      return error("binding-static-identity");
    values.push_back(value.getValue().str());
  }
  auto root = cast<ProtocolModuleOp>(op->getParentOp());
  bool physical = root.getStageAttr() && root.getStage() == "physical";
  source::OperationBinding binding{{},
                                   name.getValue().str(),
                                   contract.getValue().str(),
                                   std::move(values),
                                   implementation.getValue().str()};
  if (auto e = checkBindingDeclaration(binding, physical))
    return e;
  return binding;
}

Expected<source::OperationBinding> operationBinding(Operation *user) {
  auto root = user->getParentOfType<ProtocolModuleOp>();
  auto reference = user->getAttrOfType<FlatSymbolRefAttr>("binding");
  if (!root || !reference)
    return error("binding-reference");
  return readBinding(SymbolTable::lookupSymbolIn(root, reference));
}

LogicalResult verifyBoundOperation(Operation *op, bool physical) {
  auto selected = operationBinding(op);
  if (!selected)
    return op->emitOpError() << toString(selected.takeError());
  auto signature = resolveBinding(*selected, physical);
  if (!signature)
    return op->emitOpError() << toString(signature.takeError());
  if (physical) {
    auto key = op->getAttrOfType<StringAttr>("kernel");
    if (!isa<ExecuteKernelOp>(op) || !key ||
        key.getValue() != selected->implementation)
      return op->emitOpError("binding-implementation");
  } else if (op->getName().getStringRef() != signature->operation)
    return op->emitOpError("binding-operation");
  auto types = [&](TypeRange actual, ArrayRef<BoundType> expected) {
    if (actual.size() != expected.size())
      return false;
    for (auto [type, target] : zip(actual, expected)) {
      auto value = encodeBoundType(type, physical);
      if (!value) {
        consumeError(value.takeError());
        return false;
      }
      if (!(*value == target))
        return false;
    }
    return true;
  };
  if (!types(op->getOperandTypes(), signature->inputs) ||
      !types(op->getResultTypes(), signature->outputs))
    return op->emitOpError("binding-operation-signature");
  auto parameters = op->getAttrOfType<ArrayAttr>("parameters");
  if (!parameters)
    return op->emitOpError("binding-parameters");
  source::Names values;
  for (auto p : parameters) {
    auto value = dyn_cast<StringAttr>(p);
    if (!value)
      return op->emitOpError("binding-parameters");
    values.push_back(value.getValue().str());
  }
  if (auto e = checkParameters(selected->contract, values,
                               (selected->contract == "field.constant" ||
                                selected->contract == "vector.constant")
                                   ? signature->outputs[0].identity
                                   : ""))
    return op->emitOpError() << toString(std::move(e));
  return success();
}
} // namespace zkc::protocol

namespace zkc {
LogicalResult OperationBindingOp::verify() {
  auto binding = protocol::readBinding(*this);
  if (!binding)
    return emitOpError() << toString(binding.takeError());
  return success();
}
} // namespace zkc
