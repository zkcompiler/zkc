#include "ControlCursor.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"

using namespace mlir;
namespace zkc::exec::detail {
bool ControlCursor::inspect(Block *block) {
  return block && block->getParent() == &function.getBody() &&
         inspected.insert(block).second;
}
bool ControlCursor::enter(Block *block) {
  if (!inspect(block))
    return false;
  current = block;
  position = block->begin();
  return true;
}
bool ControlCursor::atEnd() const {
  return !current || position == current->end();
}
Operation *ControlCursor::peek() const {
  return atEnd() ? nullptr : &*position;
}
Operation *ControlCursor::take() {
  return charge() && !atEnd() ? &*position++ : nullptr;
}
bool ControlCursor::complete() const {
  return atEnd() &&
         inspected.size() == function->getRegion(0).getBlocks().size();
}
bool ControlCursor::failure(Block *block) {
  if (failed)
    return block == failed;
  if (!inspect(block) || block == current || block->getNumArguments() != 1 ||
      !isa<StopType>(block->getArgument(0).getType()) ||
      block->getOperations().size() != 2 || !charge() || !charge())
    return false;
  auto stopped = dyn_cast<FailureOp>(block->front());
  auto returned = dyn_cast<func::ReturnOp>(block->back());
  if (!stopped || !stopped->getAttrs().empty() ||
      stopped.getStop() != block->getArgument(0) ||
      TypeRange(function.getResultTypes()) !=
          TypeRange{stopped.getOutcome().getType()} ||
      !returned || !returned->getAttrs().empty() ||
      returned.getOperands() != ValueRange{stopped.getOutcome()})
    return false;
  failed = block;
  return true;
}
bool ControlCursor::dispatch(Value outcome,
                             llvm::SmallVectorImpl<Value> &payload,
                             Block *customFailure) {
  auto edge = dyn_cast_or_null<DispatchOp>(take());
  if (!edge || !edge->getAttrs().empty() || edge.getOutcome() != outcome ||
      !atEnd() ||
      !(customFailure ? edge.getStopped() == customFailure
                      : failure(edge.getStopped())) ||
      !enter(edge.getReturned()))
    return false;
  llvm::append_range(payload, current->getArguments());
  return true;
}
} // namespace zkc::exec::detail
