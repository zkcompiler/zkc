#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Interfaces/ControlFlowInterfaces.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/Execution.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "llvm/ADT/DenseSet.h"
#include <map>
#include <set>

using namespace mlir;
namespace zkc::runtime {
namespace {
bool linear(Type type) {
  if (isa<ScopeType, TransferType>(type))
    return true;
  if (auto outcome = dyn_cast<exec::OutcomeType>(type))
    return llvm::any_of(outcome.getPayload(), linear);
  return false;
}
struct ValueOrder {
  bool operator()(Value left, Value right) const {
    return std::less<const void *>()(left.getAsOpaquePointer(),
                                     right.getAsOpaquePointer());
  }
};
using Ownership = std::set<Value, ValueOrder>;
LogicalResult refuse(Operation *op, StringRef reason) {
  return diagnostics::emit(op->emitOpError(), "execution-ownership", reason);
}
LogicalResult checkOwnership(func::FuncOp function, bool scheduled) {
  // Bound structural work before recursive MLIR verification. Only the closed
  // scheduling vocabulary can introduce nested regions in this analysis.
  SmallVector<std::pair<Operation *, unsigned>> structure{{function, 0}};
  unsigned operationCount = 0;
  while (!structure.empty()) {
    auto [op, depth] = structure.pop_back_val();
    if (++operationCount > 1000000 || depth > 64)
      return refuse(function, "scope ownership structural limit");
    if (op != function && op->getNumRegions() &&
        (!scheduled || !isa<scf::WhileOp, scf::ExecuteRegionOp>(op)))
      return refuse(op,
                    "scope ownership requires its selected control profile");
    for (auto &region : op->getRegions())
      for (auto &block : region)
        for (auto &nested : block) {
          if (operationCount + structure.size() >= 1000000)
            return refuse(function, "scope ownership structural limit");
          structure.emplace_back(&nested, depth + 1);
        }
  }
  if (function.isExternal() || failed(verify(function)))
    return refuse(function, "scope ownership requires a verified body");
  Ownership borrowed, initial;
  for (Value argument : function.getArguments()) {
    if (isa<ScopeType>(argument.getType()))
      borrowed.insert(argument);
    else if (linear(argument.getType()))
      initial.insert(argument);
  }
  // Worklist points are block entries and continuations after region control.
  // Ordinary operations are traversed linearly without copying a live-owner
  // set per instruction. Backedges must reproduce the exact incoming set.
  std::map<Operation *, Ownership> incoming;
  SmallVector<Operation *> pending{&function.front().front()};
  incoming.emplace(pending.front(), std::move(initial));
  llvm::DenseSet<Operation *> visited;
  auto enqueue = [&](Operation *from, Operation *to, Ownership live) {
    if (!to)
      return refuse(from, "missing control continuation");
    auto [entry, fresh] = incoming.emplace(to, live);
    if (fresh)
      pending.push_back(to);
    else if (entry->second != live)
      return refuse(from, "incoming edges disagree on live ownership");
    return success();
  };
  auto move = [&](Operation *op, Ownership live, ValueRange operands,
                  ValueRange destinations, Operation *next) {
    if (operands.size() != destinations.size())
      return refuse(op, "ownership edge has inconsistent ports");
    SmallVector<Value> introduced;
    for (auto [operand, destination] : llvm::zip(operands, destinations)) {
      if (!linear(destination.getType()))
        continue;
      if (live.erase(operand) != 1)
        return refuse(op, "edge duplicates or forwards borrowed ownership");
      introduced.push_back(destination);
    }
    for (Value value : introduced)
      if (!live.insert(value).second)
        return refuse(op, "edge aliases an existing owner");
    return enqueue(op, next, std::move(live));
  };
  unsigned remaining = 1000000;
  while (!pending.empty()) {
    Operation *point = pending.pop_back_val();
    Ownership live = incoming.at(point);
    for (Operation *next = point; next; next = next->getNextNode()) {
      Operation &op = *next;
      if (!remaining-- || !visited.insert(&op).second)
        return refuse(&op,
                      "scope ownership analysis limit or overlapping edge");
      for (Value operand : op.getOperands())
        if (linear(operand.getType()) && !live.count(operand) &&
            !borrowed.count(operand))
          return refuse(&op, "scope or transfer used after consumption");
      // SCF edges transport ownership just like CF block arguments. The
      // condition has both successors even when it is a constant: this is a
      // conservative all-path check, not a reachability optimization.
      if (auto loop = dyn_cast<scf::WhileOp>(op)) {
        auto &before = loop.getBefore().front();
        if (failed(move(&op, live, loop.getOperands(), before.getArguments(),
                        &before.front())))
          return failure();
        break;
      }
      if (auto execute = dyn_cast<scf::ExecuteRegionOp>(op)) {
        if (execute.getRegion().empty() ||
            failed(enqueue(&op, &execute.getRegion().front().front(), live)))
          return failure();
        break;
      }
      if (auto condition = dyn_cast<scf::ConditionOp>(op)) {
        auto loop = dyn_cast<scf::WhileOp>(op.getParentOp());
        if (!scheduled || !loop || op.getParentRegion() != &loop.getBefore())
          return refuse(&op, "condition outside scheduled while");
        auto &after = loop.getAfter().front();
        if (failed(move(&op, live, condition.getArgs(), after.getArguments(),
                        &after.front())) ||
            failed(move(&op, live, condition.getArgs(), loop.getResults(),
                        loop->getNextNode())))
          return failure();
        break;
      }
      if (auto yield = dyn_cast<scf::YieldOp>(op)) {
        if (!scheduled)
          return refuse(&op, "yield outside scheduled control");
        if (auto loop = dyn_cast<scf::WhileOp>(op.getParentOp())) {
          if (op.getParentRegion() != &loop.getAfter())
            return refuse(&op, "yield outside while continuation");
          auto &before = loop.getBefore().front();
          if (failed(move(&op, live, yield.getOperands(), before.getArguments(),
                          &before.front())))
            return failure();
        } else if (auto execute =
                       dyn_cast<scf::ExecuteRegionOp>(op.getParentOp())) {
          if (failed(move(&op, live, yield.getOperands(), execute.getResults(),
                          execute->getNextNode())))
            return failure();
        } else
          return refuse(&op, "yield outside scheduled region");
        break;
      }
      auto consume = [&](Value value) {
        return !linear(value.getType()) || live.erase(value) == 1;
      };
      auto allConsumed = [&](ValueRange values) {
        return llvm::all_of(values, consume);
      };
      if (auto exit = dyn_cast<ExitScopeOp>(op)) {
        if (!allConsumed(exit->getOperands()))
          return refuse(&op, "scope exit cannot consume borrowed ownership");
      } else if (auto accept = dyn_cast<AcceptTransferOp>(op)) {
        if (!consume(accept.getTransfer()))
          return refuse(&op, "parent handoff must consume its transfer once");
      } else if (isa<ReleaseTransferOp, TakeConditionOp, exec::DispatchOp>(
                     op)) {
        if (!consume(op.getOperand(0)))
          return refuse(&op, "outcome or transfer must be consumed once");
      } else if (isa<exec::ReturnOp, func::ReturnOp>(op)) {
        if (!allConsumed(op.getOperands()))
          return refuse(&op, "borrowed ownership cannot be returned");
        if (isa<func::ReturnOp>(op) && !live.empty())
          return refuse(&op, "return bypasses scope or transfer cleanup");
      } else if (isa<EnterScopeOp, BorrowTransferOp, TransferValuesOp,
                     IterationOp, ReleaseBindingsOp, exec::ApplyOp,
                     exec::ComputeOp, exec::FoldOp, exec::CollectOp,
                     exec::CompleteOp, exec::BooleanOp, exec::RejectOp,
                     exec::TestOp, exec::RangeOp, exec::VariantOp,
                     exec::FailureOp>(op)) {
        // These operations borrow their input ownership. Their type verifiers
        // exclude nested handles in ordinary value payloads.
      } else if (isa<func::CallOp>(op)) {
        if (llvm::any_of(op.getOperands(),
                         [](Value operand) {
                           return linear(operand.getType()) &&
                                  !isa<ScopeType>(operand.getType());
                         }) ||
            llvm::any_of(op.getResultTypes(), linear))
          return refuse(&op,
                        "calls borrow scopes and return ordinary outcomes");
      } else if (isa<BranchOpInterface>(op)) {
        if (llvm::any_of(op.getResultTypes(), linear))
          return refuse(&op, "branch cannot create owned SSA results");
      } else {
        if (llvm::any_of(op.getOperandTypes(), linear) ||
            llvm::any_of(op.getResultTypes(), linear))
          return refuse(&op, "operation has no scope ownership contract");
      }
      for (Value result : op.getResults())
        if (linear(result.getType()) && !live.insert(result).second)
          return refuse(&op, "duplicate owned result");
      if (auto branch = dyn_cast<BranchOpInterface>(op)) {
        for (unsigned i = 0; i < op.getNumSuccessors(); ++i) {
          Block *destination = op.getSuccessor(i);
          Ownership outgoing = live;
          auto operands = branch.getSuccessorOperands(i);
          SmallVector<Value> introduced;
          for (unsigned j = 0; j < destination->getNumArguments(); ++j) {
            Value argument = destination->getArgument(j);
            if (!linear(argument.getType()))
              continue;
            if (operands.isOperandProduced(j) && !isa<exec::DispatchOp>(op))
              return refuse(&op,
                            "only outcome dispatch can produce edge ownership");
            if (!operands.isOperandProduced(j) &&
                outgoing.erase(operands[j]) != 1)
              return refuse(&op,
                            "edge duplicates or forwards borrowed ownership");
            introduced.push_back(argument);
          }
          for (Value argument : introduced)
            if (!outgoing.insert(argument).second)
              return refuse(&op, "edge aliases an existing owner");
          if (failed(enqueue(&op, &destination->front(), std::move(outgoing))))
            return failure();
        }
      } else if (op.hasTrait<OpTrait::IsTerminator>() &&
                 !isa<func::ReturnOp>(op)) {
        return refuse(&op, "unknown terminal ownership boundary");
      }
    }
  }
  if (visited.size() + 1 != operationCount)
    return refuse(function, "unreachable operations lack checked ownership");
  return success();
}
} // namespace
LogicalResult verifyScopeOwnership(func::FuncOp function) {
  return checkOwnership(function, false);
}
LogicalResult verifyScheduledScopeOwnership(func::FuncOp function) {
  return checkOwnership(function, true);
}
} // namespace zkc::runtime
