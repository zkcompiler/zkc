#include "OracleAnalysis.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "llvm/ADT/DenseSet.h"
using namespace mlir;
namespace zkc::mathematical {
LogicalResult verifyOracleHolder(Value root, llvm::StringRef role,
                                 Operation *use, unsigned &remaining) {
  SmallVector<Value> pending{root};
  llvm::DenseSet<Value> seen;
  auto exhausted = [&] {
    return diagnostics::emit(use->emitOpError(), "mathematical-analysis-limit",
                             "oracle holder dependency budget exhausted");
  };
  auto refuse = [&] {
    return diagnostics::emit(use->emitOpError(), "mathematical-formation",
                             "oracle contents require the holder of every "
                             "possible dynamic anchor");
  };
  auto enqueue = [&](Value value) {
    if (!remaining)
      return false;
    --remaining;
    pending.push_back(value);
    return true;
  };
  while (!pending.empty()) {
    Value value = pending.pop_back_val();
    if (!seen.insert(value).second)
      continue;
    if (!remaining)
      return exhausted();
    --remaining;
    if (auto argument = dyn_cast<BlockArgument>(value)) {
      auto repeat =
          dyn_cast<protocol_ir::RepeatOp>(argument.getOwner()->getParentOp());
      if (!repeat || failed(repeat->getName().verifyInvariants(repeat)) ||
          failed(repeat.verifyRegions()))
        return refuse();
      unsigned index = argument.getArgNumber();
      if (!enqueue(repeat.getOperand(index)))
        return exhausted();
      if (index && index <= uint64_t(repeat.getCarried()))
        if (!enqueue(repeat.getBody().front().back().getOperand(index - 1)))
          return exhausted();
      continue;
    }
    auto *producer = value.getDefiningOp();
    // Backedges can reach a producer not yet visited by enclosing formation.
    // Read its typed accessors only after checking its local invariants.
    if (!producer || failed(producer->getName().verifyInvariants(producer)) ||
        failed(verifyOperation(producer, Context::Protocol)))
      return refuse();
    if (auto send = dyn_cast<protocol_ir::OracleSendOp>(producer)) {
      if (send.getSender() != role)
        return refuse();
    } else if (auto constructed =
                   dyn_cast<protocol_ir::OracleVirtualOp>(producer)) {
      if (constructed.getHolder() != role)
        return refuse();
      for (Value input : constructed.getInputs())
        if (isa<protocol_ir::OracleHandleType>(input.getType()) &&
            !enqueue(input))
          return exhausted();
    } else if (isa<protocol_ir::OracleSequenceEmptyOp>(producer)) {
      // No anchor exists in an empty sequence. Selection from it must stop,
      // so no successful contents operation gains a fabricated anchor.
      continue;
    } else if (isa<protocol_ir::OracleForgetRowsOp,
                   protocol_ir::RestrictRolesOp,
                   protocol_ir::OracleSequenceAppendOp>(producer)) {
      for (Value input : producer->getOperands())
        if (!enqueue(input))
          return exhausted();
    } else if (auto at = dyn_cast<protocol_ir::OracleSequenceAtOp>(producer)) {
      if (!enqueue(at.getSequence()))
        return exhausted();
    } else if (auto repeat = dyn_cast<protocol_ir::RepeatOp>(producer)) {
      if (failed(repeat.verifyRegions()))
        return refuse();
      unsigned index = cast<OpResult>(value).getResultNumber();
      if (!enqueue(repeat.getOperand(index + 1)) ||
          !enqueue(repeat.getBody().front().back().getOperand(index)))
        return exhausted();
    } else
      return refuse();
  }
  return success();
}
} // namespace zkc::mathematical
