#include "zkc/Dialect/Plan/IR/Physical.h"
#include "PhysicalEncoding.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
using namespace mlir;
using namespace llvm;
namespace zkc {
Type physicalType(Type type) {
  if (auto field = dyn_cast<FieldType>(type))
    return ScalarType::get(type.getContext(), field.getDomain());
  return type;
}
Type logicalType(Type type) {
  if (auto scalar = dyn_cast<ScalarType>(type))
    return FieldType::get(type.getContext(), scalar.getDomain());
  return type;
}
bool isPhysicalProgram(Operation *op) {
  auto realization = op->getAttrOfType<StringAttr>("realization");
  return isa<PlanProgramOp>(op) && realization &&
         realization.getValue() == "table-physical-plan";
}
LogicalResult verifyPhysicalOperationContext(Operation *op) {
  Operation *program = op->getParentOp();
  while (program && !isa<PIRProgramOp, PlanProgramOp>(program))
    program = program->getParentOp();
  if (!program || !isPhysicalProgram(program))
    return diagnostics::emit(op->emitOpError(), "missing-physical-context");
  return success();
}
Expected<json::Value>
physicalDescriptor(Operation *op, const SourceLibraryInterface &library) {
  // Resolve the logical contract, then verify its changed value signature.
  // The descriptor is data, never permission to dispatch another library.
  if (op->getNumRegions() || op->getAttrDictionary().size() != 1)
    return error("invalid-physical-operation");
  json::Value logical(nullptr), descriptor(nullptr);
  if (auto prepare = dyn_cast<PrepareOp>(op)) {
    auto mode = prepare.getMode();
    if (mode != "lazy" && mode != "materialized")
      return error("unsupported-preparation-mode");
    auto view = cast<ResidualType>(prepare.getView().getType());
    logical =
        json::Array{"evaluate", view.getDomain(), naturalValue(view.getRank())};
    descriptor = json::Array{"prepare", mode, view.getDomain(),
                             naturalValue(view.getRank())};
  } else if (auto invoke = dyn_cast<InvokeOp>(op)) {
    auto parsed = parseJson(invoke.getDescriptor());
    if (!parsed)
      return parsed.takeError();
    logical = std::move(*parsed);
    descriptor = json::Array{"invoke", logical};
  } else
    return error("unsupported-physical-operation");
  Builder b(op->getContext());
  auto resolved = library.resolveOperation(logical, b);
  if (!resolved)
    return resolved.takeError();
  SmallVector<Type> inputs, outputs;
  if (resolved->ordered) {
    inputs.push_back(FlowType::get(op->getContext()));
    outputs.push_back(FlowType::get(op->getContext()));
  }
  for (Type type : resolved->inputs)
    inputs.push_back(physicalType(type));
  outputs.push_back(physicalType(resolved->output));
  if (op->getOperandTypes() != TypeRange(inputs) ||
      op->getResultTypes() != TypeRange(outputs))
    return error("physical-signature-mismatch");
  return descriptor;
}
} // namespace zkc
