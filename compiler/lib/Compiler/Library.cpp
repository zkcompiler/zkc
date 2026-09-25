#include "zkc/Compiler/Library.h"
#include "zkc/Dialect/IR.h"
#include "llvm/ADT/StringSet.h"
using namespace llvm;
using namespace mlir;
namespace zkc {
Expected<const SourceLibraryInterface *>
resolveLibrary(const json::Value &dependencies, MLIRContext &context) {
  auto *refs = dependencies.getAsArray();
  if (!refs || refs->empty())
    return error("unresolved-dependency");
  llvm::StringSet<> names;
  for (const auto &value : *refs) {
    auto *ref = value.getAsArray();
    if (!ref || ref->size() != 2 || !(*ref)[0].getAsString() ||
        !(*ref)[1].getAsString() || (*ref)[0].getAsString()->empty() ||
        (*ref)[1].getAsString()->empty() ||
        !names.insert(*(*ref)[0].getAsString()).second)
      return error("invalid-dependency");
  }
  const SourceLibraryInterface *selected = nullptr;
  for (const auto &model :
       DialectInterfaceCollection<SourceLibraryInterface>(&context)) {
    if (model.dependencies() != dependencies)
      continue;
    if (selected)
      return error("ambiguous-library");
    selected = &model;
  }
  if (!selected)
    return error("unresolved-dependency");
  return selected;
}
LogicalResult verifySourceOperationContext(Operation *op) {
  if (!isa<SourceOpInterface>(op))
    return op->emitOpError("missing-source-interface");
  Operation *program = op->getParentOp();
  while (program && !isa<PIRProgramOp, PlanProgramOp>(program))
    program = program->getParentOp();
  if (!program)
    return op->emitOpError("missing-source-context");
  return success();
}
LogicalResult verifySourceOperation(Operation *op,
                                    const ResolvedOperation &resolved) {
  Builder b(op->getContext());
  if (resolved.name != op->getName().getStringRef())
    return op->emitOpError("operation-family-mismatch");
  if (op->getAttrDictionary() != b.getDictionaryAttr(resolved.attributes))
    return op->emitOpError("unsupported-attribute");
  SmallVector<Type> inputs = resolved.inputs, outputs{resolved.output};
  if (resolved.ordered) {
    inputs.insert(inputs.begin(), FlowType::get(op->getContext()));
    outputs.insert(outputs.begin(), FlowType::get(op->getContext()));
  }
  if (op->getOperandTypes() != TypeRange(inputs) ||
      op->getResultTypes() != TypeRange(outputs))
    return op->emitOpError("operation-signature-mismatch");
  return success();
}
} // namespace zkc
