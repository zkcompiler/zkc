#include "zkc/Dialect/Exec/ControlCursor.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"

using namespace mlir;
using namespace llvm;
namespace zkc::exec {
namespace {
bool attrs(Operation *op, ArrayRef<StringRef> names = {}) {
  return op && llvm::all_of(op->getAttrs(), [&](NamedAttribute attribute) {
           return llvm::is_contained(names, attribute.getName().getValue());
         });
}
} // namespace
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
bool ControlCursor::region(StringRef kind, StringRef site, StringRef selection,
                           ValueRange inputs, RegionCheck body, unsigned index,
                           SmallVectorImpl<Value> &results) {
  Value scope = function.getArgument(0);
  auto entry = dyn_cast_or_null<runtime::EnterScopeOp>(take());
  if (!entry || entry.getParent() != scope || entry.getKind() != kind ||
      entry.getSite() != site ||
      entry.getSelection().value_or("") != selection ||
      !attrs(entry, {"kind", "site", "selection", "operandSegmentSizes"}) ||
      entry.getCoordinate() || entry.getInputs() != inputs)
    return false;
  SmallVector<Value> acquired;
  if (!dispatch(entry.getOutcome(), acquired) || acquired.size() != 1)
    return false;
  auto call = dyn_cast_or_null<func::CallOp>(take());
  SmallVector<Value> operands{acquired.front()};
  append_range(operands, entry.getInputs());
  if (!call || !attrs(call, {"callee"}) || call.getOperands() != operands ||
      call.getNumResults() != 1 || !body(call, index))
    return false;
  auto leave = dyn_cast_or_null<runtime::ExitScopeOp>(take());
  SmallVector<Value> held;
  if (!leave || !attrs(leave) || leave.getScope() != acquired.front() ||
      leave.getBody() != call.getResult(0) ||
      !dispatch(leave.getOutcome(), held) || held.size() != 1)
    return false;
  auto accept = dyn_cast_or_null<runtime::AcceptTransferOp>(take());
  return accept && attrs(accept) && accept.getParent() == scope &&
         accept.getTransfer() == held.front() &&
         dispatch(accept.getOutcome(), results);
}
bool ControlCursor::conditional(Value condition, ValueRange captures,
                                StringRef site, RegionCheck body,
                                SmallVectorImpl<Value> &results) {
  Value scope = function.getArgument(0);
  auto test = dyn_cast_or_null<exec::TestOp>(take());
  SmallVector<Value> decision;
  if (!test || !attrs(test, {"site"}) || test.getScope() != scope ||
      test.getSite() != site || test.getCondition() != condition ||
      !dispatch(test.getOutcome(), decision))
    return false;
  auto branch = dyn_cast_or_null<cf::CondBranchOp>(take());
  if (!branch || !branch->getDiscardableAttrDictionary().empty() ||
      branch.getBranchWeights() || branch.getCondition() != decision.front() ||
      !branch.getTrueDestOperands().empty() ||
      !branch.getFalseDestOperands().empty() || !atEnd())
    return false;
  Block *join = nullptr;
  for (unsigned i = 0; i < 2; ++i) {
    if (!enter(i ? branch.getFalseDest() : branch.getTrueDest()))
      return false;
    SmallVector<Value> values;
    if (!region("conditional", site, i ? "else" : "then", captures, body, i,
                values))
      return false;
    auto edge = dyn_cast_or_null<cf::BranchOp>(take());
    if (!edge || !attrs(edge) || edge.getDestOperands() != values || !atEnd() ||
        (join && join != edge.getDest()))
      return false;
    join = edge.getDest();
  }
  if (!enter(join))
    return false;
  append_range(results, current->getArguments());
  return true;
}
bool ControlCursor::match(Value input, ValueRange captures,
                          ArrayRef<std::string> alternatives, StringRef site,
                          RegionCheck body, SmallVectorImpl<Value> &results) {
  Value scope = function.getArgument(0);
  auto match = dyn_cast_or_null<exec::MatchOp>(take());
  if (!match || !attrs(match, {"site", "alternatives"}) ||
      match.getScope() != scope || match.getSite() != site || !atEnd() ||
      !failure(match.getStopped()) || match.getInput() != input ||
      match.getCaptures() != captures ||
      match.getArms().size() != alternatives.size())
    return false;
  Block *join = nullptr;
  for (auto [i, alternative] : enumerate(alternatives)) {
    auto *arm = match.getArms()[i];
    if (cast<StringAttr>(match.getAlternatives()[i]).getValue() !=
            alternative ||
        !enter(arm))
      return false;
    SmallVector<Value> values;
    if (!region("match", site, alternative, arm->getArguments(), body, i,
                values))
      return false;
    auto edge = dyn_cast_or_null<cf::BranchOp>(take());
    if (!edge || !attrs(edge) || edge.getDestOperands() != values || !atEnd() ||
        (join && join != edge.getDest()))
      return false;
    join = edge.getDest();
  }
  if (!enter(join))
    return false;
  append_range(results, current->getArguments());
  return true;
}
bool ControlCursor::loop(Value lower, Value upper, ValueRange seeds,
                         ValueRange captures, bool conditional, StringRef site,
                         RegionCheck body, SmallVectorImpl<Value> &results) {
  Value scope = function.getArgument(0);
  auto range = dyn_cast_or_null<exec::RangeOp>(take());
  SmallVector<Value> bounds;
  if (!range || !attrs(range, {"site"}) || range.getScope() != scope ||
      range.getSite() != site || range.getLower() != lower ||
      range.getUpper() != upper || !dispatch(range.getOutcome(), bounds))
    return false;
  auto initial = dyn_cast_or_null<runtime::BorrowTransferOp>(take());
  auto initialEdge = dyn_cast_or_null<cf::BranchOp>(take());
  if (!initial || !attrs(initial) || initial.getParent() != scope ||
      initial.getInputs() != seeds || !initialEdge || !attrs(initialEdge) ||
      initialEdge.getDestOperands() !=
          ValueRange{bounds[0], initial.getTransfer()} ||
      !atEnd() || !enter(initialEdge.getDest()) ||
      current->getNumArguments() != 2)
    return false;
  auto *header = current;
  Value coordinate = header->getArgument(0), previous = header->getArgument(1);
  auto compare = dyn_cast_or_null<arith::CmpIOp>(take());
  auto edge = dyn_cast_or_null<cf::CondBranchOp>(take());
  if (!compare || !attrs(compare, {"predicate"}) ||
      compare.getPredicate() != arith::CmpIPredicate::ult ||
      compare.getLhs() != coordinate || compare.getRhs() != bounds[1] ||
      !edge || !edge->getDiscardableAttrDictionary().empty() ||
      edge.getBranchWeights() || edge.getCondition() != compare.getResult() ||
      !edge.getTrueDestOperands().empty() ||
      edge.getFalseDestOperands() != ValueRange{previous} || !atEnd() ||
      !enter(edge.getTrueDest()))
    return false;
  Block *finish = edge.getFalseDest();
  auto iteration = dyn_cast_or_null<runtime::IterationOp>(take());
  if (!iteration || !attrs(iteration, {"site"}) ||
      iteration.getParent() != scope ||
      iteration.getCoordinate() != coordinate || iteration.getSite() != site)
    return false;
  auto iterationEdge = dyn_cast_or_null<exec::DispatchOp>(peek());
  if (!iterationEdge)
    return false;
  Block *cleanup = iterationEdge.getStopped();
  if (!cleanup || cleanup == current || !inspect(cleanup) ||
      cleanup->getNumArguments() != 1 || cleanup->getOperations().size() != 2 ||
      !charge() || !charge())
    return false;
  auto release = dyn_cast<runtime::ReleaseTransferOp>(cleanup->front());
  auto propagate = dyn_cast<cf::BranchOp>(cleanup->back());
  if (!release || !attrs(release) || release.getTransfer() != previous ||
      !propagate || !attrs(propagate) ||
      propagate.getDestOperands() != cleanup->getArguments() ||
      !failure(propagate.getDest()))
    return false;
  SmallVector<Value> index;
  if (!dispatch(iteration.getOutcome(), index, cleanup) || index.size() != 1 ||
      index.front().getType() != range.getLower().getType())
    return false;
  auto peek = dyn_cast_or_null<runtime::TransferValuesOp>(take());
  if (!peek || !attrs(peek) || peek.getTransfer() != previous ||
      peek.getValues().getTypes() != seeds.getTypes())
    return false;
  SmallVector<Value> bodyInputs(index);
  append_range(bodyInputs, peek.getValues());
  append_range(bodyInputs, captures);
  auto entry = dyn_cast_or_null<runtime::EnterScopeOp>(take());
  if (!entry || !attrs(entry, {"kind", "site", "operandSegmentSizes"}) ||
      entry.getParent() != scope || entry.getKind() != "iteration" ||
      entry.getCoordinate() != coordinate || entry.getSite() != site ||
      entry.getInputs() != ValueRange(bodyInputs))
    return false;
  SmallVector<Value> acquired;
  if (!dispatch(entry.getOutcome(), acquired, cleanup) || acquired.size() != 1)
    return false;
  SmallVector<Value> arguments{acquired.front()};
  append_range(arguments, entry.getInputs());
  auto call = dyn_cast_or_null<func::CallOp>(take());
  if (!call || !attrs(call, {"callee"}) || call.getOperands() != arguments ||
      call.getNumResults() != 1 || !body(call, 0))
    return false;
  auto leave = dyn_cast_or_null<runtime::ExitScopeOp>(take());
  SmallVector<Value> held;
  if (!leave || !attrs(leave) || leave.getScope() != acquired.front() ||
      leave.getBody() != call.getResult(0) ||
      !dispatch(leave.getOutcome(), held, cleanup) || held.size() != 1)
    return false;
  auto old = dyn_cast_or_null<runtime::ReleaseTransferOp>(take());
  if (!old || !attrs(old) || old.getTransfer() != previous)
    return false;
  Block *increment = nullptr;
  if (conditional) {
    auto test = dyn_cast_or_null<runtime::TakeConditionOp>(take());
    SmallVector<Value> selected;
    if (!test || !attrs(test) || test.getTransfer() != held.front() ||
        !dispatch(test.getOutcome(), selected))
      return false;
    auto branch = dyn_cast_or_null<cf::CondBranchOp>(take());
    if (!branch || !branch->getDiscardableAttrDictionary().empty() ||
        branch.getBranchWeights() || branch.getCondition() != selected[0] ||
        branch.getFalseDest() != finish ||
        branch.getTrueDestOperands() != ValueRange{selected[1]} ||
        branch.getFalseDestOperands() != ValueRange{selected[1]} || !atEnd())
      return false;
    increment = branch.getTrueDest();
  } else {
    auto branch = dyn_cast_or_null<cf::BranchOp>(take());
    if (!branch || !attrs(branch) || branch.getDestOperands() != held ||
        !atEnd())
      return false;
    increment = branch.getDest();
  }
  if (!enter(increment) || increment->getNumArguments() != 1)
    return false;
  auto one = dyn_cast_or_null<arith::ConstantIntOp>(take());
  auto advance = dyn_cast_or_null<arith::AddIOp>(take());
  auto back = dyn_cast_or_null<cf::BranchOp>(take());
  if (!one || !attrs(one, {"value"}) || one.value() != 1 ||
      !one.getType().isSignlessInteger(64) || !advance ||
      !attrs(advance, {"overflowFlags"}) ||
      advance.getOverflowFlags() != arith::IntegerOverflowFlags::none ||
      advance.getLhs() != coordinate || advance.getRhs() != one.getResult() ||
      !back || !attrs(back) || back.getDest() != header ||
      back.getDestOperands() !=
          ValueRange{advance.getResult(), increment->getArgument(0)} ||
      !atEnd() || !enter(finish) || finish->getNumArguments() != 1)
    return false;
  auto accept = dyn_cast_or_null<runtime::AcceptTransferOp>(take());
  SmallVector<Value> outputs;
  if (!accept || !attrs(accept) || accept.getParent() != scope ||
      accept.getTransfer() != finish->getArgument(0) ||
      !dispatch(accept.getOutcome(), outputs))
    return false;
  append_range(results, outputs);
  return true;
}
} // namespace zkc::exec
