#include "Storage.h"
#include "../Target/ExecutionPorts.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseMap.h"

using namespace llvm;
using namespace mlir;
using namespace zkc::target;
namespace zkc::protocol {
Error applyStorage(ModuleOp module, ArrayRef<StorageRelease> releases) {
  auto admitted = ExecutionPorts::read(module);
  if (!admitted)
    return admitted.takeError();
  const auto &flow = *admitted;
  auto operations = flow.operations();
  auto valueAt = [&](StorageValue value) -> Value {
    if (value.operation >= operations.size())
      return {};
    auto *owner = operations[value.operation];
    if (value.kind == StorageValue::OperationResult && !value.block &&
        value.index < flow.outputs(owner).size())
      return flow.outputs(owner)[value.index];
    if (value.kind == StorageValue::BlockArgument &&
        value.block < flow.get(owner).bodies.size()) {
      const auto &body = flow.body(flow.get(owner).bodies[value.block]);
      if (body.owner == owner && value.index < body.arguments.size())
        return body.arguments[value.index];
    }
    return {};
  };
  OpBuilder builder(module.getContext());
  for (const auto &release : releases) {
    const auto &point = release.point;
    if (point.operation >= operations.size() || release.values.empty() ||
        release.values.size() > 1024)
      return error("storage-materialization-correspondence");
    auto *owner = operations[point.operation];
    Block *entry = nullptr;
    Operation *before = nullptr;
    if (point.kind == StoragePoint::BlockEntry &&
        point.index < flow.get(owner).bodies.size()) {
      entry = flow.get(owner).bodies[point.index];
      const auto &body = flow.body(entry);
      if (body.owner != owner || !isa<func::FuncOp>(owner) ||
          body.instructions.empty())
        return error("storage-materialization-correspondence");
      before = body.instructions.front();
    } else if (point.kind == StoragePoint::AfterOperation && !point.index) {
      entry = flow.enclosingBody(owner);
      if (!entry)
        return error("storage-materialization-correspondence");
      const auto &instructions = flow.body(entry).instructions;
      auto position = llvm::find(instructions, owner);
      if (position == instructions.end() || ++position == instructions.end())
        return error("storage-materialization-correspondence");
      before = *position;
    } else {
      return error("storage-materialization-correspondence");
    }
    SmallVector<Value> values;
    for (auto coordinate : release.values) {
      auto value = valueAt(coordinate);
      if (!value)
        return error("storage-materialization-correspondence");
      values.push_back(value);
    }
    builder.setInsertionPoint(before);
    runtime::ReleaseBindingsOp::create(builder, before->getLoc(),
                                       entry->getArgument(0), values);
  }
  return Error::success();
}

namespace {
class StorageCorrespondence {
  std::optional<ExecutionPorts> sourcePorts, actualPorts;
  llvm::DenseMap<Operation *, size_t> indices;
  llvm::DenseMap<Value, Value> values;
  llvm::DenseMap<Value, StorageValue> coordinates;
  size_t remaining = 1000000;
  SmallVector<StorageRelease> releases;

  bool charge(size_t work = 1) {
    if (work > remaining) {
      remaining = 0;
      return false;
    }
    remaining -= work;
    return true;
  }
  bool sameRelease(Operation *source, Operation *actual) {
    if (!isa<runtime::ReleaseBindingsOp>(source) ||
        !isa<runtime::ReleaseBindingsOp>(actual) ||
        sourcePorts->inputs(source).size() !=
            actualPorts->inputs(actual).size() ||
        source->getAttrDictionary() != actual->getAttrDictionary())
      return false;
    for (auto [before, after] :
         zip(sourcePorts->inputs(source), actualPorts->inputs(actual)))
      if (values.lookup(before) != after)
        return false;
    return true;
  }
  bool added(StoragePoint point, Operation *actual) {
    auto inputs = actualPorts->inputs(actual);
    if (!isa<runtime::ReleaseBindingsOp>(actual) || inputs.empty() ||
        inputs.size() > 1024 || !actual->getAttrs().empty() ||
        !charge(inputs.size() + 1))
      return false;
    StorageRelease release{point, {}};
    for (Value input : inputs) {
      auto found = coordinates.find(input);
      if (found == coordinates.end())
        return false;
      release.values.push_back(found->second);
    }
    releases.push_back(std::move(release));
    return true;
  }
  bool function(func::FuncOp source, func::FuncOp actual) {
    if (!actual || source->getAttrDictionary() != actual->getAttrDictionary())
      return false;
    const auto &before = sourcePorts->body(&source.front());
    const auto &after = actualPorts->body(&actual.front());
    if (!charge(before.arguments.size() + 1) ||
        before.arguments.size() != after.arguments.size())
      return false;
    for (auto [index, pair] :
         enumerate(zip(before.arguments, after.arguments))) {
      values[std::get<0>(pair)] = std::get<1>(pair);
      coordinates[std::get<1>(pair)] = {StorageValue::BlockArgument,
                                        indices.lookup(source), unsigned(index),
                                        0};
    }
    size_t cursor = 0;
    StoragePoint point{StoragePoint::BlockEntry, indices.lookup(source), 0};
    for (auto *old : before.instructions) {
      while (cursor != after.instructions.size() &&
             isa<runtime::ReleaseBindingsOp>(after.instructions[cursor]) &&
             !sameRelease(old, after.instructions[cursor]))
        if (!added(point, after.instructions[cursor++]))
          return false;
      if (cursor == after.instructions.size())
        return false;
      auto *op = after.instructions[cursor++];
      const auto &left = sourcePorts->get(old), &right = actualPorts->get(op);
      if (!charge(left.inputs.size() + left.outputs.size() +
                  left.bodies.size() + 1) ||
          old->getName() != op->getName() ||
          old->getAttrDictionary() != op->getAttrDictionary() ||
          left.inputs.size() != right.inputs.size() ||
          left.outputs.size() != right.outputs.size() ||
          left.bodies.size() != right.bodies.size() ||
          left.step->conditional != right.step->conditional ||
          !llvm::equal(ValueRange(left.outputs).getTypes(),
                       ValueRange(right.outputs).getTypes()))
        return false;
      for (auto [x, y] : zip(left.inputs, right.inputs))
        if (values.lookup(x) != y)
          return false;
      for (auto [x, y] : zip(left.bodies, right.bodies))
        if (sourcePorts->body(x).owner->getAttr("sym_name") !=
            actualPorts->body(y).owner->getAttr("sym_name"))
          return false;
      for (auto [index, pair] : enumerate(zip(left.outputs, right.outputs))) {
        values[std::get<0>(pair)] = std::get<1>(pair);
        coordinates[std::get<1>(pair)] = {StorageValue::OperationResult,
                                          indices.lookup(old), unsigned(index)};
      }
      point = {StoragePoint::AfterOperation, indices.lookup(old)};
    }
    return cursor == after.instructions.size();
  }
  bool operation(Operation *source, Operation *actual, unsigned depth) {
    if (auto scoped = dyn_cast<func::FuncOp>(source))
      return function(scoped, dyn_cast<func::FuncOp>(actual));
    if (depth > 128 ||
        !charge(source->getNumOperands() + source->getNumResults() + 1) ||
        source->getName() != actual->getName() ||
        source->getAttrDictionary() != actual->getAttrDictionary() ||
        !llvm::equal(source->getResultTypes(), actual->getResultTypes()) ||
        source->getNumOperands() != actual->getNumOperands() ||
        source->getNumRegions() != actual->getNumRegions() ||
        source->getNumSuccessors() || actual->getNumSuccessors())
      return false;
    for (auto [before, after] :
         zip(source->getOperands(), actual->getOperands()))
      if (values.lookup(before) != after)
        return false;
    unsigned blockIndex = 0;
    for (auto [left, right] : zip(source->getRegions(), actual->getRegions())) {
      if (left.getBlocks().size() != right.getBlocks().size())
        return false;
      for (auto [before, after] : zip(left, right)) {
        unsigned block = blockIndex++;
        if (!llvm::equal(before.getArgumentTypes(), after.getArgumentTypes()) ||
            !charge(before.getNumArguments() + 1))
          return false;
        for (auto [a, b] : zip(before.getArguments(), after.getArguments())) {
          values[a] = b;
          coordinates.insert(
              {b,
               {StorageValue::BlockArgument, indices.lookup(source),
                a.getArgNumber(), block}});
        }
        auto cursor = after.begin();
        for (Operation &old : before)
          if (cursor == after.end() || !operation(&old, &*cursor++, depth + 1))
            return false;
        if (cursor != after.end())
          return false;
      }
    }
    for (auto [before, after] :
         zip(source->getResults(), actual->getResults())) {
      values[before] = after;
      coordinates.insert({after,
                          {StorageValue::OperationResult,
                           indices.lookup(source), before.getResultNumber()}});
    }
    return true;
  }

public:
  Expected<SmallVector<StorageRelease>> check(ModuleOp before, ModuleOp after) {
    auto beforeView = ExecutionPorts::read(before);
    if (!beforeView)
      return beforeView.takeError();
    auto afterView = ExecutionPorts::read(after);
    if (!afterView)
      return afterView.takeError();
    sourcePorts = std::move(*beforeView);
    actualPorts = std::move(*afterView);
    for (auto [index, op] : enumerate(sourcePorts->operations()))
      indices[op] = index;
    if (!operation(before, after, 0))
      return error(remaining ? "storage-correspondence"
                             : "storage-schedule-limit");
    return std::move(releases);
  }
};
} // namespace

Expected<SmallVector<StorageRelease>> readStorageReleases(ModuleOp before,
                                                          ModuleOp after) {
  return StorageCorrespondence().check(before, after);
}
Error verifyStorageMaterialization(ModuleOp before, ModuleOp after,
                                   ArrayRef<StorageRelease> expected) {
  auto actual = readStorageReleases(before, after);
  if (!actual)
    return actual.takeError();
  // Group by stable point, preserving chunk and operand order at that point.
  // Regions may be visited in a different order by producer and reader.
  std::map<StoragePoint, SmallVector<const StorageRelease *>> left, right;
  for (const auto &release : expected)
    left[release.point].push_back(&release);
  for (const auto &release : *actual)
    right[release.point].push_back(&release);
  if (left.size() != right.size())
    return error("storage-materialization-correspondence");
  for (const auto &[point, chunks] : left) {
    auto found = right.find(point);
    if (found == right.end() || chunks.size() != found->second.size())
      return error("storage-materialization-correspondence");
    for (auto [a, b] : zip(chunks, found->second))
      if (!(*a == *b))
        return error("storage-materialization-correspondence");
  }
  return Error::success();
}
} // namespace zkc::protocol
