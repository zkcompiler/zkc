#include "Storage.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseMap.h"

using namespace llvm;
using namespace mlir;
using namespace zkc::target;
namespace zkc::protocol {
namespace {
bool releaseShape(Operation *op) {
  return isa<plan::ReleaseOp>(op) && !op->getNumResults() &&
         !op->getNumRegions() && !op->getNumSuccessors() &&
         op->getAttrs().empty() && op->getNumOperands() &&
         op->getNumOperands() <= 1024;
}
} // namespace

Error applyStorage(ModuleOp module, ArrayRef<StorageRelease> releases,
                   ArrayRef<Operation *> operations,
                   ArrayRef<SmallVector<Value>> conversions) {
  if (releases.empty())
    return Error::success();
  SmallVector<SmallVector<Block *>> blocks(operations.size());
  for (auto [index, op] : enumerate(operations))
    for (auto &region : op->getRegions())
      for (auto &block : region)
        blocks[index].push_back(&block);
  auto blockAt = [&](size_t operation, unsigned block) -> Block * {
    return block < blocks[operation].size() ? blocks[operation][block]
                                            : nullptr;
  };
  auto valueAt = [&](StorageValue value) -> Value {
    if (value.operation >= operations.size())
      return {};
    auto *owner = operations[value.operation];
    switch (value.kind) {
    case StorageValue::OperationResult:
      if (!value.block && value.index < owner->getNumResults())
        return owner->getResult(value.index);
      break;
    case StorageValue::BlockArgument:
      if (auto *block = blockAt(value.operation, value.block))
        if (value.index < block->getNumArguments())
          return block->getArgument(value.index);
      break;
    case StorageValue::ConversionResult:
      if (!value.block && value.operation < conversions.size() &&
          value.index < conversions[value.operation].size())
        return conversions[value.operation][value.index];
      break;
    }
    return {};
  };
  OpBuilder builder(module.getContext());
  std::map<StoragePoint, Operation *> tails;
  for (const auto &release : releases) {
    auto at = release.point;
    if (at.operation >= operations.size() || release.values.empty() ||
        release.values.size() > 1024)
      return error("storage-materialization-correspondence");
    auto tail = tails.find(at);
    if (tail != tails.end()) {
      builder.setInsertionPointAfter(tail->second);
    } else {
      auto *owner = operations[at.operation];
      switch (at.kind) {
      case StoragePoint::BlockEntry: {
        auto *block = blockAt(at.operation, at.index);
        if (!block)
          return error("storage-materialization-correspondence");
        builder.setInsertionPointToStart(block);
        break;
      }
      case StoragePoint::AfterConversion: {
        auto value =
            valueAt({StorageValue::ConversionResult, at.operation, at.index});
        if (!value || !value.getDefiningOp())
          return error("storage-materialization-correspondence");
        builder.setInsertionPointAfter(value.getDefiningOp());
        break;
      }
      case StoragePoint::AfterOperation:
        if (at.index || owner->hasTrait<OpTrait::IsTerminator>())
          return error("storage-materialization-correspondence");
        builder.setInsertionPointAfter(owner);
        break;
      default:
        return error("storage-materialization-correspondence");
      }
    }
    SmallVector<Value> operands;
    for (auto coordinate : release.values) {
      Value value = valueAt(coordinate);
      if (!value)
        return error("storage-materialization-correspondence");
      operands.push_back(value);
    }
    auto inserted =
        plan::ReleaseOp::create(builder, builder.getUnknownLoc(), operands);
    tails[at] = inserted;
  }
  return Error::success();
}

StorageReleaseReader::StorageReleaseReader(ArrayRef<StorageRelease> releases)
    : expected(releases.size()) {
  for (const auto &release : releases)
    points[release.point].push_back(&release);
}
bool StorageReleaseReader::read(StoragePoint point, Block &block,
                                Block::iterator &cursor,
                                llvm::function_ref<Value(StorageValue)> valueAt,
                                size_t &remaining) {
  auto found = points.find(point);
  if (found == points.end())
    return true;
  for (const auto *release : found->second) {
    if (cursor == block.end() || !releaseShape(&*cursor) ||
        cursor->getNumOperands() != release->values.size())
      return false;
    size_t work = cursor->getNumOperands() + 1;
    if (work > remaining) {
      remaining = 0;
      return false;
    }
    remaining -= work;
    for (auto [operand, coordinate] :
         zip(cursor->getOperands(), release->values)) {
      Value value = valueAt(coordinate);
      if (!value || operand != value)
        return false;
    }
    ++cursor;
    ++consumed;
  }
  points.erase(found);
  return true;
}

namespace {
class StorageCorrespondence {
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
    if (!isa<plan::ReleaseOp>(source) || !isa<plan::ReleaseOp>(actual) ||
        source->getNumOperands() != actual->getNumOperands() ||
        source->getAttrDictionary() != actual->getAttrDictionary())
      return false;
    for (auto [before, after] :
         zip(source->getOperands(), actual->getOperands()))
      if (values.lookup(before) != after)
        return false;
    return true;
  }
  bool added(StoragePoint point, Operation *actual) {
    if (!releaseShape(actual) || !charge(actual->getNumOperands() + 1))
      return false;
    StorageRelease release{point, {}};
    for (Value operand : actual->getOperands()) {
      auto found = coordinates.find(operand);
      if (found == coordinates.end())
        return false;
      release.values.push_back(found->second);
    }
    releases.push_back(std::move(release));
    return true;
  }
  bool operation(Operation *source, Operation *actual, unsigned depth) {
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
        StoragePoint point{StoragePoint::BlockEntry, indices.lookup(source),
                           block};
        auto cursor = after.begin();
        for (Operation &old : before) {
          while (cursor != after.end() && isa<plan::ReleaseOp>(*cursor) &&
                 !sameRelease(&old, &*cursor)) {
            if (!added(point, &*cursor++))
              return false;
          }
          if (cursor == after.end() || !operation(&old, &*cursor++, depth + 1))
            return false;
          point = {StoragePoint::AfterOperation, indices.lookup(&old)};
        }
        while (cursor != after.end() && isa<plan::ReleaseOp>(*cursor))
          if (!added(point, &*cursor++))
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
    bool exceeded = false;
    before->walk<WalkOrder::PreOrder>([&](Operation *op) {
      if (indices.size() == remaining) {
        exceeded = true;
        return WalkResult::interrupt();
      }
      size_t index = indices.size();
      indices[op] = index;
      return WalkResult::advance();
    });
    if (exceeded)
      return error("storage-schedule-limit");
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
