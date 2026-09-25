#include "Support.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Protocol/Bindings.h"
#include "zkc/Protocol/Kernels.h"
#include "zkc/Protocol/TypeProperties.h"
#include "llvm/ADT/DenseMap.h"

using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
LogicalResult releaseLocalStorage(ModuleOp module) {
  if (failed(verify(module)))
    return failure();
  if (!llvm::hasSingleElement(*module.getBody()))
    return module.emitError("interactive-release-context");
  auto root = dyn_cast<ProtocolModuleOp>(&module.getBody()->front());
  if (!root || root.getStage() != "physical")
    return module.emitError("interactive-release-context");
  for (auto function : root.getBody().front().getOps<func::FuncOp>()) {
    if (!llvm::hasSingleElement(function.getBody()))
      return function.emitError("interactive-release-context");
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
          return function.emitError() << toString(type.takeError());
        bool canDiscard = discardable(type->spelling());
        if (!canDiscard)
          continue;
        Operation *end = last.lookup(value);
        // An affine last use already consumes its permission. A storage release
        // would be a second use, even when that kind permits unused values to
        // drop.
        if (end && affine(type->spelling()))
          continue;
        if (end && isa<func::ReturnOp, LocalYieldOp, ReleaseOp>(end))
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
          operation(builder, "plan.release", chunk);
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
} // namespace zkc::protocol
