#include "OracleAnalysis.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "llvm/ADT/DenseMap.h"
using namespace mlir;
namespace zkc::mathematical {
namespace {
// An application environment substitutes formal values lazily. No expanded IR
// is allocated and the seen key includes the actual application environment.
class InitialShape {
  enum class Meaning : uint8_t { Value = 1, Handle = 2 };
  struct Scope {
    protocol_ir::MathematicalOp program;
    protocol_ir::ApplyOp call;
    unsigned parent = 0, depth = 0;
  };
  struct Work {
    Value value;
    unsigned scope;
    Meaning meaning;
  };
  Operation *use;
  SymbolTableCollection &symbols;
  unsigned &remaining;
  SmallVector<Scope> scopes;
  SmallVector<Work> pending;
  llvm::DenseMap<std::pair<Operation *, unsigned>, unsigned> applications;
  llvm::DenseMap<std::pair<Value, unsigned>, uint8_t> seen;
  LogicalResult refuse(llvm::StringRef reason) {
    return diagnostics::emit(use->emitOpError(), "mathematical-formation",
                             reason);
  }
  LogicalResult charge() {
    if (!remaining)
      return diagnostics::emit(use->emitOpError(),
                               "mathematical-analysis-limit",
                               "oracle shape dependency budget exhausted");
    --remaining;
    return success();
  }
  LogicalResult add(Value value, unsigned scope, Meaning meaning) {
    if (failed(charge()))
      return failure();
    pending.push_back({value, scope, meaning});
    return success();
  }
  FailureOr<unsigned> application(protocol_ir::ApplyOp call, unsigned parent) {
    auto key = std::make_pair(call.getOperation(), parent);
    if (auto found = applications.find(key); found != applications.end())
      return found->second;
    if (failed(charge()) || failed(call.verifySymbolUses(symbols)))
      return failure();
    auto callee = symbols.lookupNearestSymbolFrom<protocol_ir::MathematicalOp>(
        call, call.getCalleeAttr());
    auto &body = callee.getBody().front();
    unsigned depth = scopes[parent].depth + 1;
    if (depth > 64 ||
        body.getArgumentTypes() != callee.getFunctionType().getInputs() ||
        body.back().getOperandTypes() !=
            callee.getFunctionType().getResults()) {
      (void)refuse(
          "oracle shape requires a bounded, formed application closure");
      return failure();
    }
    unsigned index = scopes.size();
    scopes.push_back({callee, call, parent, depth});
    applications[key] = index;
    return index;
  }
  LogicalResult loop(protocol_ir::RepeatOp repeat, unsigned index, Work item,
                     bool argument) {
    if (failed(repeat->getName().verifyInvariants(repeat)) ||
        failed(repeat.verifyRegions()) ||
        failed(add(repeat.getOperand(index), item.scope, item.meaning)))
      return failure();
    if (index && (index <= uint64_t(repeat.getCarried()) || !argument))
      if (failed(add(repeat.getInputs().front(), item.scope, Meaning::Value)) ||
          failed(add(repeat.getBody().front().back().getOperand(index - 1),
                     item.scope, item.meaning)))
        return failure();
    return success();
  }
  LogicalResult visit(Work item) {
    auto [value, scope, meaning] = item;
    auto &visited = seen[{value, scope}];
    if (visited & uint8_t(meaning))
      return success();
    visited |= uint8_t(meaning);
    if (meaning == Meaning::Handle)
      if (auto type = dyn_cast<protocol_ir::OracleHandleType>(value.getType());
          type && type.getKind().getStaticRows())
        return success();
    if (auto argument = dyn_cast<BlockArgument>(value)) {
      auto environment = scopes[scope];
      if (argument.getOwner() == &environment.program.getBody().front()) {
        if (environment.call)
          return add(environment.call.getOperand(argument.getArgNumber()),
                     environment.parent, meaning);
        return meaning == Meaning::Value
                   ? success()
                   : refuse("oracle shape requires a bound entry anchor");
      }
      auto repeat =
          dyn_cast<protocol_ir::RepeatOp>(argument.getOwner()->getParentOp());
      return repeat
                 ? loop(repeat, argument.getArgNumber(), item, true)
                 : refuse("oracle shape depends on a foreign block argument");
    }
    auto *op = value.getDefiningOp();
    if (!op || failed(op->getName().verifyInvariants(op)))
      return refuse("malformed oracle shape dependency");
    if (auto repeat = dyn_cast<protocol_ir::RepeatOp>(op))
      return loop(repeat, cast<OpResult>(value).getResultNumber() + 1, item,
                  false);
    if (auto call = dyn_cast<protocol_ir::ApplyOp>(op)) {
      auto nested = application(call, scope);
      if (failed(nested))
        return failure();
      return add(scopes[*nested].program.getBody().front().back().getOperand(
                     cast<OpResult>(value).getResultNumber()),
                 *nested, meaning);
    }
    if (meaning == Meaning::Value) {
      if (auto rows = dyn_cast<protocol_ir::OracleRowsOp>(op))
        return add(rows.getHandle(), scope, Meaning::Handle);
      if (isTotal(op) || isa<func::CallOp, protocol_ir::RestrictRolesOp>(op)) {
        for (Value input : op->getOperands())
          if (failed(add(input, scope, Meaning::Value)))
            return failure();
        return success();
      }
      return refuse("oracle shape cannot depend on messages, sampling, queries "
                    "or execution");
    }
    if (auto send = dyn_cast<protocol_ir::OracleSendOp>(op))
      return add(send.getRows(), scope, Meaning::Value);
    if (auto input = dyn_cast<protocol_ir::OracleInputOp>(op)) {
      auto raw = dyn_cast<BlockArgument>(input.getAnchor());
      if (!scope && raw &&
          raw.getOwner() == &scopes[0].program.getBody().front()) {
        // Both root components are initial input. In a call, follow the actual
        // passed anchor instead: its dimensions need not be initial data.
        if (failed(add(input.getData(), scope, Meaning::Value)))
          return failure();
        return add(input.getAnchor(), scope, Meaning::Value);
      }
      return add(input.getAnchor(), scope, Meaning::Handle);
    }
    if (auto constructed = dyn_cast<protocol_ir::OracleVirtualOp>(op)) {
      auto declaration =
          symbols.lookupNearestSymbolFrom<protocol_ir::OracleDefinitionOp>(
              constructed, constructed.getCalleeAttr());
      if (!declaration ||
          failed(declaration->getName().verifyInvariants(declaration)) ||
          failed(declaration.verifyRegions()) ||
          failed(constructed.verifySymbolUses(symbols)) ||
          !declaration.getShapeArgument())
        return refuse("oracle shape requires its actual virtual declaration");
      return add(constructed.getInputs()[*declaration.getShapeArgument()],
                 scope, Meaning::Value);
    }
    if (isa<protocol_ir::OracleForgetRowsOp, protocol_ir::RestrictRolesOp,
            protocol_ir::OracleSequenceAppendOp,
            protocol_ir::OracleComponentsOp>(op)) {
      for (Value input : op->getOperands())
        if (failed(add(input, scope, Meaning::Handle)))
          return failure();
      return success();
    }
    if (auto at = dyn_cast<protocol_ir::OracleSequenceAtOp>(op)) {
      if (failed(add(at.getSequence(), scope, Meaning::Handle)))
        return failure();
      return add(at.getPosition(), scope, Meaning::Value);
    }
    if (isa<protocol_ir::OracleSequenceEmptyOp>(op))
      return success();
    return refuse(
        "oracle shape requires a bound input, send or virtual anchor");
  }

public:
  InitialShape(protocol_ir::MathematicalOp program, Operation *use,
               SymbolTableCollection &symbols, unsigned &remaining)
      : use(use), symbols(symbols), remaining(remaining),
        scopes{{program, {}}} {}
  LogicalResult run(Value root) {
    if (failed(add(root, 0, Meaning::Value)))
      return failure();
    while (!pending.empty())
      if (failed(visit(pending.pop_back_val())))
        return failure();
    return success();
  }
};
} // namespace
LogicalResult verifyInitialOracleShape(Value value,
                                       protocol_ir::MathematicalOp program,
                                       Operation *use,
                                       SymbolTableCollection &symbols,
                                       unsigned &remaining) {
  return InitialShape(program, use, symbols, remaining).run(value);
}
} // namespace zkc::mathematical
