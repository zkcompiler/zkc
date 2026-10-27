#include "../Target/ExecutionPorts.h"
#include "../Target/PhysicalPlan.h"
#include "Bindings.h"
#include "Storage.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
namespace {
class PhysicalCorrespondence {
  const target::PhysicalPlan &plan;
  std::optional<target::ExecutionPorts> sourcePorts, actualPorts;
  std::map<target::StoragePoint, SmallVector<const target::StorageRelease *>>
      releasePoints;
  size_t releasesConsumed = 0;
  std::map<target::StorageValue, Value> storageValues;
  llvm::DenseMap<Operation *, unsigned> indices;
  llvm::DenseMap<Value, Value> values;
  llvm::DenseSet<Operation *> newBindings;
  llvm::StringMap<const target::BindingDecision *> added;
  llvm::DenseMap<unsigned, const target::BindingDecision *> originals;
  size_t remaining = 1000000;
  bool charge() { return remaining && (--remaining, true); }
  bool binding(runtime::BindingOp op,
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
    auto physical = op.getPhysicalArgumentsAttr();
    if (!physical ||
        physical.size() != expected.application.physicalArguments.size())
      return false;
    for (auto [actual, argument] :
         zip(physical, expected.application.physicalArguments))
      if (cast<StringAttr>(actual).getValue() != argument)
        return false;
    return op->getAttrs().size() == 5;
  }
  bool application(Operation *op, const protocol::OperationBinding &binding,
                   ValueRange operands, TypeRange results, Attribute site,
                   ArrayAttr parameters) {
    if (!op || !charge() || !isa<exec::ApplyOp>(op) || op->getNumRegions() ||
        op->getAttrs().size() != 3 ||
        !llvm::equal(actualPorts->inputs(op), operands) ||
        !llvm::equal(actualPorts->outputs(op).getTypes(), results) ||
        op->getAttr("site") != site || op->getAttr("parameters") != parameters)
      return false;
    auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding");
    return reference && reference.getValue() == binding.name;
  }
  bool skipBindings(Block &block, Block::iterator &cursor) {
    while (cursor != block.end()) {
      auto op = dyn_cast<runtime::BindingOp>(*cursor);
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
  bool releases(target::StoragePoint point, ArrayRef<Operation *> actual,
                size_t &cursor) {
    auto found = releasePoints.find(point);
    if (found == releasePoints.end())
      return true;
    for (auto *chunk : found->second) {
      if (cursor == actual.size() || !charge())
        return false;
      auto *op = actual[cursor++];
      if (!isa<runtime::ReleaseBindingsOp>(op) || !op->getAttrs().empty() ||
          actualPorts->inputs(op).size() != chunk->values.size() ||
          !actualPorts->outputs(op).empty())
        return false;
      for (auto [coordinate, input] :
           zip(chunk->values, actualPorts->inputs(op))) {
        auto value = storageValues.find(coordinate);
        if (!charge() || value == storageValues.end() || value->second != input)
          return false;
      }
      ++releasesConsumed;
    }
    return true;
  }
  bool function(func::FuncOp source, func::FuncOp actual) {
    const auto &choice = plan.operations[indices.lookup(source)];
    if (!actual || !charge())
      return false;
    SmallVector<Type> inputs{runtime::ScopeType::get(source.getContext())};
    append_range(inputs, choice.functionType.getInputs());
    auto result = exec::OutcomeType::get(
        source.getContext(),
        SmallVector<Type>(choice.functionType.getResults()));
    NamedAttrList attrs(source->getAttrs());
    attrs.set("function_type", TypeAttr::get(FunctionType::get(
                                   source.getContext(), inputs, result)));
    if (attrs.getDictionary(source.getContext()) != actual->getAttrDictionary())
      return false;
    const auto &before = sourcePorts->body(&source.front());
    const auto &after = actualPorts->body(&actual.front());
    if (before.arguments.size() != after.arguments.size())
      return false;
    for (auto [port, pair] :
         enumerate(zip(before.arguments, after.arguments))) {
      values[std::get<0>(pair)] = std::get<1>(pair);
      storageValues[{target::StorageValue::BlockArgument,
                     indices.lookup(source), unsigned(port), 0}] =
          std::get<1>(pair);
    }
    size_t cursor = 0;
    if (!releases({target::StoragePoint::BlockEntry, indices.lookup(source), 0},
                  after.instructions, cursor))
      return false;
    for (auto *old : before.instructions) {
      if (!charge())
        return false;
      auto index = indices.lookup(old);
      const auto &decision = plan.operations[index];
      SmallVector<Value> operands;
      for (auto value : sourcePorts->inputs(old)) {
        auto mapped = values.lookup(value);
        if (!charge() || !mapped)
          return false;
        operands.push_back(mapped);
      }
      for (auto [crossingIndex, crossing] : enumerate(decision.conversions)) {
        if (cursor == after.instructions.size() ||
            crossing.operand >= operands.size())
          return false;
        auto *conversion = after.instructions[cursor++];
        if (!application(conversion, plan.bindings[crossing.binding].binding,
                         ValueRange{operands[crossing.operand]},
                         TypeRange{crossing.to},
                         StringAttr::get(old->getContext(), crossing.site),
                         ArrayAttr::get(old->getContext(), {})))
          return false;
        operands[crossing.operand] = actualPorts->outputs(conversion).front();
        storageValues[{target::StorageValue::ConversionResult, index,
                       unsigned(crossingIndex)}] = operands[crossing.operand];
        if (!releases({target::StoragePoint::AfterConversion, index,
                       unsigned(crossingIndex)},
                      after.instructions, cursor))
          return false;
      }
      if (cursor == after.instructions.size())
        return false;
      auto *replacement = after.instructions[cursor++];
      const auto &oldNode = sourcePorts->get(old);
      const auto &newNode = actualPorts->get(replacement);
      if (decision.binding) {
        if (!application(replacement, plan.bindings[*decision.binding].binding,
                         operands, decision.outputs, old->getAttr("site"),
                         old->getAttrOfType<ArrayAttr>("parameters")))
          return false;
      } else {
        auto name = isa<exec::ReturnOp>(old)
                        ? exec::CompleteOp::getOperationName()
                        : old->getName().getStringRef();
        if (replacement->getName().getStringRef() != name ||
            replacement->getAttrDictionary() != old->getAttrDictionary() ||
            !llvm::equal(newNode.inputs, operands) ||
            !llvm::equal(ValueRange(newNode.outputs).getTypes(),
                         decision.outputs))
          return false;
      }
      if (oldNode.bodies.size() != newNode.bodies.size() ||
          oldNode.step->conditional != newNode.step->conditional ||
          oldNode.outputs.size() != newNode.outputs.size())
        return false;
      for (auto [left, right] : zip(oldNode.bodies, newNode.bodies))
        if (sourcePorts->body(left).owner->getAttr("sym_name") !=
            actualPorts->body(right).owner->getAttr("sym_name"))
          return false;
      for (auto [port, pair] :
           enumerate(zip(oldNode.outputs, newNode.outputs))) {
        values[std::get<0>(pair)] = std::get<1>(pair);
        storageValues[{target::StorageValue::OperationResult, index,
                       unsigned(port)}] = std::get<1>(pair);
      }
      if (!releases({target::StoragePoint::AfterOperation, index},
                    after.instructions, cursor))
        return false;
    }
    return cursor == after.instructions.size();
  }
  bool operation(Operation *source, Operation *actual, unsigned depth) {
    if (!charge() || depth > 128)
      return false;
    if (auto scoped = dyn_cast<func::FuncOp>(source))
      return function(scoped, dyn_cast<func::FuncOp>(actual));
    const auto &decision = plan.operations[indices.lookup(source)];
    SmallVector<Value> operands;
    for (Value input : source->getOperands()) {
      Value value = values.lookup(input);
      if (!value)
        return false;
      operands.push_back(value);
    }
    if (decision.binding) {
      if (!application(actual, plan.bindings[*decision.binding].binding,
                       operands, decision.outputs, source->getAttr("site"),
                       source->getAttrOfType<ArrayAttr>("parameters")))
        return false;
    } else {
      auto name = source->getName().getStringRef();
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
      if (isa<runtime::BindingOp>(source)) {
        auto index = indices.lookup(source);
        auto selected = originals.lookup(index);
        if (!selected)
          return false;
        SmallVector<Attribute> parameters;
        for (const auto &parameter :
             selected->binding.application.physicalArguments)
          parameters.push_back(
              StringAttr::get(source->getContext(), parameter));
        attributes.set("physical_arguments",
                       ArrayAttr::get(source->getContext(), parameters));
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
        if (before.getNumArguments() != after.getNumArguments())
          return false;
        if (!before.getArguments().empty()) {
          if (blockIndex >= decision.blockArguments.size() ||
              !llvm::equal(after.getArgumentTypes(),
                           decision.blockArguments[blockIndex]))
            return false;
        }
        if (blockIndex < decision.blockArguments.size())
          ++blockIndex;
        for (auto [x, y] : zip(before.getArguments(), after.getArguments()))
          values[x] = y;
        auto cursor = after.begin();
        for (Operation &old : before) {
          if (!skipBindings(after, cursor))
            return false;
          if (cursor == after.end() || !operation(&old, &*cursor++, depth + 1))
            return false;
        }
        if (!skipBindings(after, cursor) || cursor != after.end())
          return false;
      }
    }
    if (blockIndex != decision.blockArguments.size())
      return false;
    for (auto [x, y] : zip(source->getResults(), actual->getResults())) {
      values[x] = y;
      if (!plan.releases.empty())
        storageValues[{target::StorageValue::OperationResult,
                       indices.lookup(source), x.getResultNumber()}] = y;
    }
    return true;
  }

public:
  PhysicalCorrespondence(ModuleOp before, const target::PhysicalPlan &plan)
      : plan(plan) {
    for (const auto &release : plan.releases)
      releasePoints[release.point].push_back(&release);
    for (auto [index, op] : enumerate(target::physicalPlanOperations(before)))
      indices[op] = index;
    for (const auto &decision : plan.bindings)
      if (decision.purpose != target::BindingPurpose::Original)
        added[decision.binding.name] = &decision;
      else
        originals[*decision.declaration] = &decision;
  }
  Error check(ModuleOp before, ModuleOp after) {
    auto sourceView = target::ExecutionPorts::read(before);
    if (!sourceView)
      return sourceView.takeError();
    auto actualView = target::ExecutionPorts::read(after);
    if (!actualView)
      return actualView.takeError();
    sourcePorts = std::move(*sourceView);
    actualPorts = std::move(*actualView);
    if (!operation(before, after, 0) || newBindings.size() != added.size() ||
        releasesConsumed != plan.releases.size())
      return error(remaining ? "binding-materialization-correspondence"
                             : "binding-materialization-limit");
    return Error::success();
  }
};
} // namespace
Error verifyPhysicalMaterialization(
    ModuleOp before, ModuleOp after,
    const target::CheckedPhysicalPlan &checked) {
  auto selected = checked.choices().selectedSubject(before);
  if (!selected)
    return selected.takeError();
  if (failed(verify(before)) || failed(verify(after)))
    return error("binding-materialization-formation");
  // Decisions index this exact selected executable subject, never original
  // numerical operations. Its numerical edge was checked before constructing
  // the checked plan; reading actual physical output requires no numerical
  // producer.
  if (auto e = PhysicalCorrespondence(*selected, checked.choices())
                   .check(*selected, after))
    return e;
  // Preserve the existing participant/source postcondition on the physical
  // edge. Kernel frontier/interface changes belong to the independently checked
  // original-to-execution edge, not an unchecked exception to preservation.
  if (failed(mathematical::verifyProjectionPreserved(*selected, after)))
    return error("mathematical-projection");
  return Error::success();
}
} // namespace zkc::protocol
