#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Protocol/Execution.h"
#include "zkc/Dialect/detail/Builders.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Protocol.h"
#include "llvm/ADT/DenseMap.h"

using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
static LogicalResult insertStorageReleases(ModuleOp module) {
  if (failed(verify(module)))
    return failure();
  if (!llvm::hasSingleElement(*module.getBody()))
    return diagnostics::emit(module.emitError(), "interactive-release-context");
  auto root =
      dyn_cast<zkc::protocol_ir::ProtocolModuleOp>(&module.getBody()->front());
  if (!root || root.getProfile() != zkc::protocol_ir::Profile::Physical)
    return diagnostics::emit(module.emitError(), "interactive-release-context");
  for (auto function : root.getBody().front().getOps<zkc::local::FuncOp>()) {
    if (!llvm::hasSingleElement(function.getBody()))
      return diagnostics::emit(function.emitError(),
                               "interactive-release-context");
    SmallVector<Block *> blocks;
    function.walk([&](Operation *op) {
      for (auto &region : op->getRegions())
        for (auto &block : region)
          blocks.push_back(&block);
    });
    for (auto *current : blocks) {
      auto &block = *current;
      // Isolated regions have independent borrow handles and local last uses.
      // Existing releases count as uses, making repeated application
      // idempotent.
      llvm::DenseMap<Value, Operation *> last;
      for (auto &op : block)
        for (auto input : op.getOperands())
          last[input] = &op;
      SmallVector<Value> values(block.getArguments());
      for (auto &op : block)
        llvm::append_range(values, op.getResults());
      llvm::DenseMap<Operation *, SmallVector<Value>> after;
      SmallVector<Value> entry;
      for (Value value : values) {
        auto type = encodeBoundType(value.getType(), true);
        if (!type)
          return diagnostics::emit(function.emitError(), type.takeError());
        bool canDiscard = discardable(type->spelling());
        if (!canDiscard)
          continue;
        Operation *end = last.lookup(value);
        // An affine last use already consumes its permission. A storage release
        // would be a second use, even when that kind permits unused values to
        // drop.
        if (end && affine(type->spelling()))
          continue;
        if (end && isa<zkc::local::ReturnOp, zkc::local::LocalYieldOp,
                       zkc::local::LocalConditionOp, zkc::plan::ReleaseOp>(end))
          continue;
        if (!end)
          end = value.getDefiningOp();
        if (end)
          after[end].push_back(value);
        else
          entry.push_back(value);
      }
      OpBuilder builder(module.getContext());
      auto emit = [&](ArrayRef<Value> dead) {
        while (!dead.empty()) {
          auto chunk = dead.take_front(1024);
          zkc::plan::ReleaseOp::create(builder, builder.getUnknownLoc(), chunk);
          dead = dead.drop_front(chunk.size());
        }
      };
      builder.setInsertionPointToStart(&block);
      emit(entry);
      // Walk block order rather than DenseMap order for deterministic output.
      for (auto &op : llvm::make_early_inc_range(block)) {
        auto found = after.find(&op);
        if (found != after.end()) {
          builder.setInsertionPointAfter(&op);
          emit(found->second);
        }
      }
    }
  }
  return verify(module);
}
namespace {
// Remove only newly inserted releases from a comparison clone. Existing
// releases must keep their operand identities and position among computations.
bool removeAddedReleases(Operation *before, Operation *after,
                         llvm::DenseMap<Value, Value> &values, unsigned depth) {
  if (depth > 128 || before->getName() != after->getName() ||
      before->getNumRegions() != after->getNumRegions() ||
      before->getNumResults() != after->getNumResults())
    return false;
  for (auto [left, right] : zip(before->getRegions(), after->getRegions())) {
    if (left.getBlocks().size() != right.getBlocks().size())
      return false;
    for (auto [source, candidate] : zip(left, right)) {
      if (source.getNumArguments() != candidate.getNumArguments())
        return false;
      for (auto [a, b] : zip(source.getArguments(), candidate.getArguments()))
        values[a] = b;
      auto cursor = candidate.begin();
      for (Operation &op : source) {
        auto matchesRelease = [&](Operation &actual) {
          if (!isa<plan::ReleaseOp>(op) ||
              op.getNumOperands() != actual.getNumOperands())
            return false;
          for (auto [a, b] : zip(op.getOperands(), actual.getOperands()))
            if (values.lookup(a) != b)
              return false;
          return true;
        };
        while (cursor != candidate.end() && isa<plan::ReleaseOp>(*cursor) &&
               !matchesRelease(*cursor))
          (cursor++)->erase();
        if (cursor == candidate.end() ||
            !removeAddedReleases(&op, &*cursor++, values, depth + 1))
          return false;
      }
      while (cursor != candidate.end() && isa<plan::ReleaseOp>(*cursor))
        (cursor++)->erase();
      if (cursor != candidate.end())
        return false;
    }
  }
  for (auto [a, b] : zip(before->getResults(), after->getResults()))
    values[a] = b;
  return true;
}
} // namespace
LogicalResult verifyStoragePreserved(ModuleOp before, ModuleOp after) {
  // Full module formation separately checks legal kinds, last use, custody,
  // affine consumption (through executable admission) and region escape. The
  // comparison covers every actual local body and declaration.
  if (failed(verify(before)) || failed(verify(after)))
    return failure();
  auto physical = [](ModuleOp module) {
    if (!llvm::hasSingleElement(*module.getBody()))
      return false;
    auto root =
        dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
    return root && root.getProfile() == protocol_ir::Profile::Physical;
  };
  if (!physical(before) || !physical(after))
    return diagnostics::emit(after.emitError(), "storage-correspondence-stage");
  OwningOpRef<ModuleOp> normalized(cast<ModuleOp>(after->clone()));
  llvm::DenseMap<Value, Value> values;
  if (!removeAddedReleases(before, normalized->getOperation(), values, 0) ||
      !OperationEquivalence::isEquivalentTo(
          before, normalized->getOperation(),
          OperationEquivalence::IgnoreLocations))
    return diagnostics::emit(after.emitError(), "storage-correspondence");
  return success();
}
LogicalResult releaseLocalStorage(ModuleOp module) {
  OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(module->clone()));
  if (failed(insertStorageReleases(*candidate)) ||
      failed(verifyStoragePreserved(module, *candidate)))
    return failure();
  module.getBodyRegion().takeBody(candidate->getBodyRegion());
  return success();
}
} // namespace zkc::protocol
