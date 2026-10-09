#include "../Target/PhysicalPlan.h"
#include "Bindings.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
namespace {
class PhysicalCorrespondence {
  const target::PhysicalPlan &plan;
  llvm::DenseMap<Operation *, unsigned> indices;
  llvm::DenseMap<Value, Value> values;
  llvm::DenseSet<Operation *> newBindings;
  llvm::StringMap<const target::BindingDecision *> added;
  llvm::DenseMap<unsigned, const target::BindingDecision *> originals;
  unsigned remaining = 1000000;
  bool charge() { return remaining && (--remaining, true); }
  bool binding(local::OperationBindingOp op,
               const protocol::OperationBinding &expected) {
    if (!op || op.getSymName() != expected.name ||
        op.getContract() != expected.application.contract ||
        op.getImplementation() != expected.application.implementation ||
        op.getArguments().size() != expected.application.arguments.size())
      return false;
    for (auto [actual, argument] :
         zip(op.getArguments(), expected.application.arguments))
      if (cast<StringAttr>(actual).getValue() != argument)
        return false;
    return op->getAttrs().size() == 4;
  }
  bool kernel(Operation *op, const protocol::OperationBinding &binding,
              ValueRange operands, TypeRange results, Attribute site,
              ArrayAttr parameters) {
    if (!op || !charge() || !isa<plan::ExecuteKernelOp>(op) ||
        op->getNumRegions() || op->getAttrs().size() != 4 ||
        !llvm::equal(op->getOperands(), operands) ||
        !llvm::equal(op->getResultTypes(), results) ||
        op->getAttr("site") != site || op->getAttr("parameters") != parameters)
      return false;
    auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding");
    auto implementation = op->getAttrOfType<StringAttr>("kernel");
    return reference && reference.getValue() == binding.name &&
           implementation &&
           implementation.getValue() == binding.application.implementation;
  }
  bool skipBindings(Block &block, Block::iterator &cursor) {
    while (cursor != block.end()) {
      auto op = dyn_cast<local::OperationBindingOp>(*cursor);
      if (!op)
        break;
      auto found = added.find(op.getSymName());
      if (found == added.end())
        break;
      if (!charge() || !binding(op, found->second->binding) ||
          !newBindings.insert(op).second)
        return false;
      ++cursor;
    }
    return true;
  }
  bool operation(Operation *source, Operation *actual, unsigned depth) {
    if (!charge() || depth > 128)
      return false;
    const auto &decision = plan.operations[indices.lookup(source)];
    SmallVector<Value> operands;
    for (Value input : source->getOperands()) {
      Value value = values.lookup(input);
      if (!value)
        return false;
      operands.push_back(value);
    }
    // Conversions are read by the enclosing block before this operation.
    // Each crossing is attached to its actual consumer operand below.
    auto converted = conversions.find(source);
    if (converted != conversions.end())
      operands = converted->second;
    if (decision.binding) {
      if (!kernel(actual, plan.bindings[*decision.binding].binding, operands,
                  decision.outputs, source->getAttr("site"),
                  source->getAttrOfType<ArrayAttr>("parameters")))
        return false;
    } else {
      auto name = source->getName().getStringRef();
      if (isa<local::BoolConstantOp>(source))
        name = plan::BoolConstantOp::getOperationName();
      if (actual->getName().getStringRef() != name ||
          !llvm::equal(actual->getOperands(), operands) ||
          !llvm::equal(actual->getResultTypes(), decision.outputs))
        return false;
      NamedAttrList attributes(source->getAttrs());
      if (isa<protocol_ir::ProtocolModuleOp>(source))
        attributes.set("profile", protocol_ir::ProfileAttr::get(
                                      source->getContext(),
                                      protocol_ir::Profile::Physical));
      if (decision.functionType)
        attributes.set("function_type", TypeAttr::get(decision.functionType));
      if (isa<local::OperationBindingOp>(source)) {
        auto index = indices.lookup(source);
        auto selected = originals.lookup(index);
        if (!selected)
          return false;
        attributes.set(
            "implementation",
            StringAttr::get(source->getContext(),
                            selected->binding.application.implementation));
      }
      if (attributes.getDictionary(source->getContext()) !=
          actual->getAttrDictionary())
        return false;
    }
    if (source->getNumRegions() != actual->getNumRegions())
      return false;
    unsigned blockIndex = 0;
    for (auto [left, right] : zip(source->getRegions(), actual->getRegions())) {
      if (left.getBlocks().size() != right.getBlocks().size())
        return false;
      for (auto [before, after] : zip(left, right)) {
        if (blockIndex >= decision.blockArguments.size() ||
            before.getNumArguments() != after.getNumArguments() ||
            !llvm::equal(after.getArgumentTypes(),
                         decision.blockArguments[blockIndex++]))
          return false;
        for (auto [x, y] : zip(before.getArguments(), after.getArguments()))
          values[x] = y;
        auto cursor = after.begin();
        for (Operation &old : before) {
          if (!skipBindings(after, cursor))
            return false;
          const auto &choice = plan.operations[indices.lookup(&old)];
          SmallVector<Value> inputs;
          for (Value input : old.getOperands())
            inputs.push_back(values.lookup(input));
          for (const auto &crossing : choice.conversions) {
            if (cursor == after.end() || crossing.operand >= inputs.size())
              return false;
            auto *conversion = &*cursor++;
            if (!kernel(conversion, plan.bindings[crossing.binding].binding,
                        ValueRange{inputs[crossing.operand]},
                        TypeRange{crossing.to},
                        StringAttr::get(old.getContext(), crossing.site),
                        ArrayAttr::get(old.getContext(), {})))
              return false;
            inputs[crossing.operand] = conversion->getResult(0);
          }
          if (!choice.conversions.empty())
            conversions[&old] = std::move(inputs);
          if (cursor == after.end() || !operation(&old, &*cursor++, depth + 1))
            return false;
        }
        if (!skipBindings(after, cursor) || cursor != after.end())
          return false;
      }
    }
    if (blockIndex != decision.blockArguments.size())
      return false;
    for (auto [x, y] : zip(source->getResults(), actual->getResults()))
      values[x] = y;
    return true;
  }
  llvm::DenseMap<Operation *, SmallVector<Value>> conversions;

public:
  PhysicalCorrespondence(ModuleOp before, const target::PhysicalPlan &plan)
      : plan(plan) {
    for (auto [index, op] : enumerate(target::physicalPlanOperations(before)))
      indices[op] = index;
    for (const auto &decision : plan.bindings)
      if (decision.purpose != target::BindingPurpose::Original)
        added[decision.binding.name] = &decision;
      else
        originals[*decision.declaration] = &decision;
  }
  Error check(ModuleOp before, ModuleOp after) {
    if (!operation(before, after, 0) || newBindings.size() != added.size())
      return error(remaining ? "binding-materialization-correspondence"
                             : "binding-materialization-limit");
    return Error::success();
  }
};
} // namespace
Error verifyPhysicalMaterialization(
    ModuleOp before, ModuleOp after,
    const target::CheckedPhysicalPlan &checked) {
  if (auto e = checked.checkInput(before))
    return e;
  if (failed(verify(before)) || failed(verify(after)))
    return error("binding-materialization-formation");
  return PhysicalCorrespondence(before, checked.choices()).check(before, after);
}
} // namespace zkc::protocol
