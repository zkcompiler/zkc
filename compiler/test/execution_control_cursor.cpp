#include "../lib/Dialect/Exec/ControlCursor.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
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
  auto file = llvm::MemoryBuffer::getFile(
      ZKC_FIXTURES "/runtime/execution-source-helpers.mlir");
  require(bool(file), "missing scope fixture");
  auto parse = [&] {
    auto module = parseSourceString<ModuleOp>((*file)->getBuffer(), &context);
    require(module && succeeded(verify(*module)), "invalid source fixture");
    return module;
  };
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
  return cases.result();
}
