#include "../lib/Dialect/Exec/ControlCursor.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "llvm/Support/MemoryBuffer.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
void consumeReturned(exec::detail::ControlCursor &cursor) {
  require(isa_and_nonnull<exec::ReturnOp>(cursor.take()) &&
              isa_and_nonnull<func::ReturnOp>(cursor.take()) && cursor.atEnd(),
          "unexpected source return shape");
}
} // namespace
int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto parseFixture = [&](StringRef name) {
    auto file = llvm::MemoryBuffer::getFile(std::string(ZKC_FIXTURES) +
                                            "/runtime/execution-" + name.str() +
                                            ".mlir");
    require(bool(file), "missing scope fixture");
    auto module = parseSourceString<ModuleOp>((*file)->getBuffer(), &context);
    require(module && succeeded(verify(*module)), "invalid source fixture");
    return module;
  };
  auto parse = [&] { return parseFixture("source-helpers"); };
  cases.run(
      "actual returned edge and local failure consume the whole body", [&] {
        auto module = parse();
        auto function = module->lookupSymbol<func::FuncOp>("sum");
        unsigned remaining = 20;
        exec::detail::ControlCursor cursor(function, remaining);
        require(cursor.enter(&function.front()), "entry refused");
        auto *peeked = cursor.peek();
        auto invocation = dyn_cast_or_null<exec::ApplyOp>(cursor.take());
        require(invocation && peeked == invocation.getOperation() &&
                    remaining == 19,
                "peek changed position or work");
        SmallVector<Value> payload;
        require(cursor.dispatch(invocation.getOutcome(), payload) &&
                    payload.size() == 1 &&
                    payload.front() == cursor.currentBlock()->getArgument(0),
                "dispatch lost actual returned value");
        consumeReturned(cursor);
        require(cursor.complete() && remaining == 14,
                "body inventory or shared work differs");
      });
  cases.run("all cursors debit the same consumer allowance", [&] {
    auto module = parse();
    auto function = module->lookupSymbol<func::FuncOp>("sum");
    unsigned remaining = 1;
    exec::detail::ControlCursor first(function, remaining),
        second(function, remaining);
    require(first.enter(&function.front()) && second.enter(&function.front()),
            "entry refused");
    require(first.take() && remaining == 0 && !second.take() && !first.take(),
            "nested cursor replenished work");
  });
  cases.run("foreign blocks and revisits cannot consume an owned body", [&] {
    auto module = parse();
    auto function = module->lookupSymbol<func::FuncOp>("sum");
    unsigned remaining = 20;
    exec::detail::ControlCursor cursor(function, remaining);
    require(!cursor.enter(
                &module->lookupSymbol<func::FuncOp>("identity").front()) &&
                cursor.enter(&function.front()) &&
                !cursor.enter(&function.front()),
            "cursor accepted foreign or repeated block");
  });
  cases.run(
      "a different same-typed invocation outcome cannot select the edge", [&] {
        auto module = parse();
        auto function = module->lookupSymbol<func::FuncOp>("sum");
        auto other = cast<exec::ApplyOp>(
            module->lookupSymbol<func::FuncOp>("difference").front().front());
        unsigned remaining = 20;
        exec::detail::ControlCursor cursor(function, remaining);
        require(cursor.enter(&function.front()) && cursor.take(),
                "entry refused");
        SmallVector<Value> payload;
        require(!cursor.dispatch(other.getOutcome(), payload),
                "outcome identity ignored");
      });
  cases.run("failure cannot resume with an ordinary returned payload", [&] {
    auto module = parse();
    auto function = module->lookupSymbol<func::FuncOp>("sum");
    exec::FailureOp failed;
    function.walk([&](exec::FailureOp op) { failed = op; });
    OpBuilder builder(failed);
    auto result = exec::ReturnOp::create(builder, failed.getLoc(),
                                         failed.getOutcome().getType(),
                                         ValueRange{function.getArgument(1)});
    failed.getOutcome().replaceAllUsesWith(result.getOutcome());
    failed.erase();
    require(succeeded(verify(*module)), "formed failure mutation refused");
    unsigned remaining = 20;
    exec::detail::ControlCursor cursor(function, remaining);
    require(cursor.enter(&function.front()), "entry refused");
    auto invocation = cast<exec::ApplyOp>(cursor.take());
    SmallVector<Value> payload;
    require(!cursor.dispatch(invocation.getOutcome(), payload),
            "failure recovered a value");
  });
  cases.run("unvisited additional block prevents completion", [&] {
    auto module = parse();
    auto function = module->lookupSymbol<func::FuncOp>("sum");
    auto *extra = new Block;
    function.getBody().push_back(extra);
    auto argument = extra->addArgument(function.getResultTypes().front(),
                                       function.getLoc());
    OpBuilder builder(&context);
    builder.setInsertionPointToEnd(extra);
    func::ReturnOp::create(builder, function.getLoc(), argument);
    require(succeeded(verify(*module)), "formed unreachable block refused");
    unsigned remaining = 20;
    exec::detail::ControlCursor cursor(function, remaining);
    require(cursor.enter(&function.front()), "entry refused");
    auto invocation = cast<exec::ApplyOp>(cursor.take());
    SmallVector<Value> payload;
    require(cursor.dispatch(invocation.getOutcome(), payload),
            "valid dispatch refused");
    consumeReturned(cursor);
    require(!cursor.complete(), "unvisited block escaped the owned inventory");
  });

  auto finish = [&](exec::detail::ControlCursor &cursor, ValueRange values) {
    auto completion = dyn_cast_or_null<exec::CompleteOp>(cursor.take());
    auto returned = dyn_cast_or_null<func::ReturnOp>(cursor.take());
    return completion && completion.getValues() == values && returned &&
           returned.getOperands() == ValueRange{completion.getOutcome()} &&
           cursor.complete();
  };
  cases.run("conditional skeleton supplies actual ordered calls and join", [&] {
    auto module = parseFixture("conditional");
    auto function = module->lookupSymbol<func::FuncOp>("work");
    unsigned remaining = 1000, checked = 0;
    exec::detail::ControlCursor cursor(function, remaining);
    require(cursor.enter(&function.front()), "missing entry");
    SmallVector<Value> outputs;
    require(cursor.conditional(
                function.getArgument(1), function.getArguments().drop_front(2),
                "choose",
                [&](func::CallOp call, unsigned arm) {
                  require(checked++ == arm &&
                              call.getCallee() == (arm ? "no" : "yes"),
                          "actual ordered call was not supplied");
                  return true; // This test checks the skeleton; body checks
                               // belong to the consumer.
                },
                outputs) &&
                checked == 2 && finish(cursor, outputs),
            "conditional shape refused");
  });
  for (unsigned refusedArm : {0u, 1u})
    cases.run("conditional callback refusal in arm " +
                  std::to_string(refusedArm),
              [&] {
                auto module = parseFixture("conditional");
                auto function = module->lookupSymbol<func::FuncOp>("work");
                unsigned remaining = 1000, checked = 0;
                exec::detail::ControlCursor cursor(function, remaining);
                require(cursor.enter(&function.front()), "missing entry");
                SmallVector<Value> outputs;
                require(!cursor.conditional(
                            function.getArgument(1),
                            function.getArguments().drop_front(2), "choose",
                            [&](func::CallOp, unsigned arm) {
                              ++checked;
                              return arm != refusedArm;
                            },
                            outputs) &&
                            checked == refusedArm + 1 && outputs.empty() &&
                            !cursor.complete(),
                        "callback refusal lost");
              });
  cases.run("conditional same-typed capture substitution is refused", [&] {
    auto module = parseFixture("conditional");
    auto function = module->lookupSymbol<func::FuncOp>("work");
    unsigned remaining = 1000;
    exec::detail::ControlCursor cursor(function, remaining);
    require(cursor.enter(&function.front()), "missing entry");
    SmallVector<Value> outputs;
    require(!cursor.conditional(
                function.getArgument(1),
                {function.getArgument(3), function.getArgument(2)}, "choose",
                [](func::CallOp, unsigned) { return true; }, outputs),
            "capture order lost");
  });
  for (bool acceptBody : {true, false})
    cases.run(
        acceptBody ? "loop supplies actual scoped body and published carry"
                   : "loop body refusal does not publish carry",
        [&] {
          auto module = parseFixture("loop");
          auto function = module->lookupSymbol<func::FuncOp>("loop");
          unsigned remaining = 1000, checked = 0;
          exec::detail::ControlCursor cursor(function, remaining);
          require(cursor.enter(&function.front()), "missing entry");
          SmallVector<Value> outputs;
          bool accepted = cursor.loop(
              function.getArgument(1), function.getArgument(2),
              function.getArgument(3), function.getArgument(4), true, "iterate",
              [&](func::CallOp call, unsigned arm) {
                require(call.getCallee() == "step" && arm == 0,
                        "actual iteration call lost");
                ++checked;
                return acceptBody;
              },
              outputs);
          require(accepted == acceptBody && checked == 1 &&
                      (acceptBody ? finish(cursor, outputs) : outputs.empty()),
                  "loop callback decision differs");
        });
  cases.run("loop exact range arguments are bound", [&] {
    auto module = parseFixture("loop");
    auto function = module->lookupSymbol<func::FuncOp>("loop");
    unsigned remaining = 1000;
    exec::detail::ControlCursor cursor(function, remaining);
    require(cursor.enter(&function.front()), "missing entry");
    SmallVector<Value> outputs;
    require(!cursor.loop(
                function.getArgument(2), function.getArgument(1),
                function.getArgument(3), function.getArgument(4), true,
                "iterate", [](func::CallOp, unsigned) { return true; },
                outputs),
            "same-typed bounds swapped");
  });
  cases.run("conditional loop cannot be read as unconditional", [&] {
    auto module = parseFixture("loop");
    auto function = module->lookupSymbol<func::FuncOp>("loop");
    unsigned remaining = 1000;
    exec::detail::ControlCursor cursor(function, remaining);
    require(cursor.enter(&function.front()), "missing entry");
    SmallVector<Value> outputs;
    require(!cursor.loop(
                function.getArgument(1), function.getArgument(2),
                function.getArgument(3), function.getArgument(4), false,
                "iterate", [](func::CallOp, unsigned) { return true; },
                outputs),
            "conditional carry decision disappeared");
  });
  cases.run(
      "loop failure must release current carry rather than initial borrow",
      [&] {
        auto module = parseFixture("loop");
        auto function = module->lookupSymbol<func::FuncOp>("loop");
        runtime::BorrowTransferOp initial;
        function.walk([&](runtime::BorrowTransferOp op) { initial = op; });
        function.walk([&](runtime::ReleaseTransferOp op) {
          if (op->getBlock()->getNumArguments() == 1 &&
              isa<exec::StopType>(op->getBlock()->getArgument(0).getType()))
            op.setOperand(initial.getTransfer());
        });
        require(succeeded(verify(*module)), "formed cleanup mutation refused");
        unsigned remaining = 1000;
        exec::detail::ControlCursor cursor(function, remaining);
        require(cursor.enter(&function.front()), "missing entry");
        SmallVector<Value> outputs;
        require(!cursor.loop(
                    function.getArgument(1), function.getArgument(2),
                    function.getArgument(3), function.getArgument(4), true,
                    "iterate", [](func::CallOp, unsigned) { return true; },
                    outputs),
                "stale carry cleanup accepted");
      });
  cases.run("match supplies actual payload call and published join", [&] {
    auto module = parseFixture("match");
    auto function = module->lookupSymbol<func::FuncOp>("select");
    unsigned remaining = 1000, checked = 0;
    exec::detail::ControlCursor cursor(function, remaining);
    require(cursor.enter(&function.front()), "missing entry");
    SmallVector<Value> outputs;
    require(cursor.match(
                function.getArgument(1), function.getArgument(2), {"some"},
                "select",
                [&](func::CallOp call, unsigned arm) {
                  require(call.getCallee() == "payload" && arm == 0,
                          "actual match body lost");
                  ++checked;
                  return true;
                },
                outputs) &&
                checked == 1 && finish(cursor, outputs),
            "match shape refused");
  });
  for (bool wrongLabel : {false, true})
    cases.run(wrongLabel ? "match alternative identity is bound"
                         : "match callback refusal prevents publication",
              [&] {
                auto module = parseFixture("match");
                auto function = module->lookupSymbol<func::FuncOp>("select");
                unsigned remaining = 1000, checked = 0;
                exec::detail::ControlCursor cursor(function, remaining);
                require(cursor.enter(&function.front()), "missing entry");
                SmallVector<Value> outputs;
                require(!cursor.match(
                            function.getArgument(1), function.getArgument(2),
                            {wrongLabel ? "other" : "some"}, "select",
                            [&](func::CallOp, unsigned) {
                              ++checked;
                              return false;
                            },
                            outputs) &&
                            checked == (wrongLabel ? 0u : 1u) &&
                            outputs.empty(),
                        "match refusal lost");
              });
  for (StringRef name : {"conditional", "loop", "match"})
    cases.run(
        "control work allowance covers every operation in " + name.str(), [&] {
          auto module = parseFixture(name);
          auto function =
              module->lookupSymbol<func::FuncOp>(name == "conditional" ? "work"
                                                 : name == "loop" ? "loop"
                                                                  : "select");
          unsigned operationCount = 0;
          for (Block &block : function.getBody())
            operationCount += block.getOperations().size();
          for (bool enough : {true, false}) {
            unsigned remaining = operationCount - (enough ? 0 : 1);
            exec::detail::ControlCursor cursor(function, remaining);
            require(cursor.enter(&function.front()), "missing entry");
            SmallVector<Value> outputs;
            auto body = [](func::CallOp, unsigned) { return true; };
            bool accepted =
                name == "conditional"
                    ? cursor.conditional(function.getArgument(1),
                                         function.getArguments().drop_front(2),
                                         "choose", body, outputs)
                : name == "loop"
                    ? cursor.loop(
                          function.getArgument(1), function.getArgument(2),
                          function.getArgument(3), function.getArgument(4),
                          true, "iterate", body, outputs)
                    : cursor.match(function.getArgument(1),
                                   function.getArgument(2), {"some"}, "select",
                                   body, outputs);
            accepted = accepted && finish(cursor, outputs);
            require(accepted == enough && remaining == 0,
                    "shared work accounting differs");
          }
        });
  return cases.result();
}
