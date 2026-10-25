#include "mlir/IR/Verifier.h"
#include "mlir/Interfaces/ControlFlowInterfaces.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/Execution.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
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
} // namespace

LogicalResult verifyScopeOwnership(func::FuncOp function) {
  if (function.isExternal() || failed(verify(function)))
    return refuse(function, "scope ownership requires a verified body");
  Ownership borrowed, initial;
  for (Value argument : function.getArguments()) {
    if (isa<ScopeType>(argument.getType()))
      borrowed.insert(argument);
    else if (linear(argument.getType()))
      initial.insert(argument);
  }
  std::map<Block *, Ownership> incoming;
  SmallVector<Block *> pending{&function.front()};
  incoming.emplace(&function.front(), std::move(initial));
  unsigned remaining = 1000000;
  while (!pending.empty()) {
    Block *block = pending.pop_back_val();
    Ownership live = incoming.at(block);
    for (Operation &op : *block) {
      if (!remaining--)
        return refuse(&op, "scope ownership analysis limit");
      if (op.getNumRegions())
        return refuse(&op, "scope ownership requires flat CFG regions");
      for (Value operand : op.getOperands())
        if (linear(operand.getType()) && !live.count(operand) &&
            !borrowed.count(operand))
          return refuse(&op, "scope or transfer used after consumption");
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
          auto [entry, fresh] = incoming.emplace(destination, outgoing);
          if (fresh)
            pending.push_back(destination);
          else if (entry->second != outgoing)
            return refuse(&op, "incoming edges disagree on live ownership");
        }
      } else if (op.hasTrait<OpTrait::IsTerminator>() &&
                 !isa<func::ReturnOp>(op)) {
        return refuse(&op, "unknown terminal ownership boundary");
      }
    }
  }
  if (incoming.size() != function.getBody().getBlocks().size())
    return refuse(function, "unreachable blocks lack checked ownership");
  return success();
}
} // namespace zkc::runtime
