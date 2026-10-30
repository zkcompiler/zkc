#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/ControlCursor.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/Execution.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
template <class T> T first(func::FuncOp function) {
  T result;
  function.walk([&](T op) {
    if (!result)
      result = op;
  });
  require(bool(result), "missing mutation subject");
  return result;
}
void sourceReturn(func::FuncOp function) {
  exec::CompleteOp completion;
  function.walk([&](exec::CompleteOp op) { completion = op; });
  require(bool(completion), "missing root completion");
  OpBuilder builder(completion);
  auto returned = exec::ReturnOp::create(builder, completion.getLoc(),
                                         completion.getOutcome().getType(),
                                         completion.getValues());
  completion.getOutcome().replaceAllUsesWith(returned.getOutcome());
  completion.erase();
}
bool read(func::FuncOp function, unsigned &remaining, bool conditional = true,
          unsigned loops = 1, bool acceptBody = true) {
  exec::ControlCursor cursor(function, remaining);
  if (!cursor.enter(&function.front()))
    return false;
  SmallVector<Value> values{function.getArgument(3)};
  for (unsigned i = 0; i < loops; ++i) {
    SmallVector<Value> next;
    if (!cursor.scheduledLoop(
            function.getArgument(1), function.getArgument(2), values,
            function.getArgument(4), conditional,
            i ? "iterate_next" : "iterate",
            [&](func::CallOp call, unsigned arm) {
              return acceptBody && arm == 0 && call.getCallee() == "step";
            },
            next))
      return false;
    values = next;
  }
  auto completion = dyn_cast_or_null<exec::CompleteOp>(cursor.take());
  auto returned = dyn_cast_or_null<func::ReturnOp>(cursor.take());
  return completion && completion.getValues() == ValueRange(values) &&
         returned &&
         returned.getOperands() == ValueRange{completion.getOutcome()} &&
         cursor.complete();
}
} // namespace
int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  registry.insert<scf::SCFDialect>();
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto parse = [&] {
    auto module = parseSourceFile<ModuleOp>(
        std::string(ZKC_FIXTURES) + "/runtime/execution-scheduled-loop.mlir",
        &context);
    require(module && succeeded(verify(*module)),
            "authored SCF fixture refused");
    return module;
  };
  cases.run(
      "independently authored SCF preserves custody and early stopping", [&] {
        auto module = parse();
        auto function = module->lookupSymbol<func::FuncOp>("loop");
        unsigned remaining = 10000;
        require(read(function, remaining), "actual SCF schedule refused");
        require(succeeded(runtime::verifyScheduledScopeOwnership(function)),
                "scheduled ownership refused");
        auto native = protocol::readSourceExecutionClosure(*module);
        require(!native, "transient schedule widened executable admission");
        llvm::consumeError(native.takeError());
      });
  cases.run(
      "actual SCF closure agrees with independently authored executable", [&] {
        auto schedule = parse();
        auto function = schedule->lookupSymbol<func::FuncOp>("loop");
        sourceReturn(function);
        auto actual = protocol::readScheduledExecutionClosure(*schedule);
        require(bool(actual), actual ? "" : llvm::toString(actual.takeError()));
        auto flat = parseSourceFile<ModuleOp>(
            std::string(ZKC_FIXTURES) + "/runtime/execution-loop.mlir",
            &context);
        require(bool(flat), "missing independent flat fixture");
        sourceReturn(flat->lookupSymbol<func::FuncOp>("loop"));
        auto error = protocol::verifySourceExecutionDefinitions(
            *flat,
            take(protocol::readScheduledExecutionDefinitions(*schedule)));
        require(!error, error ? llvm::toString(std::move(error)) : "");
        auto &step = actual->bodies.at("loop").front();
        require(step.operation == first<exec::RangeOp>(function) &&
                    step.inputs == SmallVector<Value>(
                                       function.getArguments().drop_front()) &&
                    step.outputs.size() == 1 && step.conditional &&
                    step.regions.size() == 1 &&
                    step.regions.front().getSymName() == "step",
                "scheduled SSA association was reconstructed incorrectly");
        auto source = protocol::readSourceExecutionClosure(*schedule);
        require(!source, "schedule widened ordinary source admission");
        llvm::consumeError(source.takeError());
      });
  cases.run(
      "SCF reader shares exact operation allowance including nested blocks",
      [&] {
        auto module = parse();
        auto function = module->lookupSymbol<func::FuncOp>("loop");
        unsigned count = 0;
        function.walk([&](Operation *op) { count += op != function; });
        for (bool enough : {true, false}) {
          unsigned remaining = count - (enough ? 0 : 1);
          require(read(function, remaining) == enough && remaining == 0,
                  "nested SCF inspection was not bounded exactly");
        }
      });
  for (bool conditional : {false, true})
    for (unsigned loops : {1u, 2u})
      cases.run(
          "builder retains scoped loop semantics: " +
              std::to_string(conditional) + "/" + std::to_string(loops),
          [&] {
            auto module = parse();
            auto function = module->lookupSymbol<func::FuncOp>("loop");
            auto step = module->lookupSymbol<func::FuncOp>("step");
            OpBuilder builder(&context);
            if (!conditional) {
              step.setType(builder.getFunctionType(step.getArgumentTypes(),
                                                   function.getResultTypes()));
              step.getBody().dropAllReferences();
              step.getBody().getBlocks().clear();
              step.addEntryBlock();
              builder.setInsertionPointToEnd(&step.front());
              exec::ScopedExecutionBuilder body(builder, step);
              body.complete(step.getArgument(2));
            }
            function.getBody().dropAllReferences();
            function.getBody().getBlocks().clear();
            function.addEntryBlock();
            builder.setInsertionPointToEnd(&function.front());
            exec::ScopedExecutionBuilder control(builder, function);
            SmallVector<Value> values{function.getArgument(3)};
            for (unsigned i = 0; i < loops; ++i)
              values = control.scheduledLoop(
                  function.getArgument(1), function.getArgument(2), values,
                  function.getArgument(4), values.front().getType(),
                  conditional, i ? "iterate_next" : "iterate",
                  [&](unsigned) { return step; });
            control.complete(values);
            require(succeeded(verify(*module)), "producer formed invalid SCF");
            unsigned remaining = 10000;
            require(read(function, remaining, conditional, loops),
                    "producer disagrees with reader");
            require(succeeded(runtime::verifyScheduledScopeOwnership(function)),
                    "produced schedule lost ownership");
            sourceReturn(function);
            auto admitted = protocol::readScheduledExecutionClosure(*module);
            require(bool(admitted),
                    admitted ? "" : llvm::toString(admitted.takeError()));
          });
  cases.run("body refusal and missing conditional result cannot publish state",
            [&] {
              auto module = parse();
              auto function = module->lookupSymbol<func::FuncOp>("loop");
              unsigned remaining = 10000;
              require(!read(function, remaining, true, 1, false),
                      "body refusal ignored");
              remaining = 10000;
              require(!read(function, remaining, false),
                      "conditional result discarded");
            });
  for (StringRef mutation :
       {"upper bound", "continuation", "stop continuation", "stride",
        "coordinate", "stale cleanup", "scope", "carry", "extra action",
        "unreachable block", "attribute"})
    cases.run("formed SCF mutation refused: " + mutation, [&] {
      auto module = parse();
      auto function = module->lookupSymbol<func::FuncOp>("loop");
      auto loop = first<scf::WhileOp>(function);
      auto packet = first<scf::ExecuteRegionOp>(function);
      if (mutation == "upper bound") {
        auto comparison = first<arith::CmpIOp>(function);
        comparison.setOperand(1, comparison.getLhs());
      } else if (mutation == "continuation") {
        auto condition = first<scf::ConditionOp>(function);
        condition.setOperand(0, first<arith::CmpIOp>(function).getResult());
      } else if (mutation == "stop continuation") {
        packet.walk([&](arith::ConstantIntOp op) {
          op.setValueAttr(IntegerAttr::get(op.getType(), 1));
        });
      } else if (mutation == "stride") {
        auto advance = first<arith::AddIOp>(function);
        auto constant = advance.getRhs().getDefiningOp<arith::ConstantIntOp>();
        constant.setValueAttr(IntegerAttr::get(constant.getType(), 2));
      } else if (mutation == "coordinate") {
        auto entry = first<runtime::EnterScopeOp>(function);
        entry->setOperand(1, loop.getOperand(0));
      } else if (mutation == "stale cleanup") {
        auto initial = first<runtime::BorrowTransferOp>(function);
        function.walk([&](runtime::ReleaseTransferOp op) {
          if (op->getBlock()->getNumArguments() == 1 &&
              isa<exec::StopType>(op->getBlock()->getArgument(0).getType()))
            op.setOperand(initial.getTransfer());
        });
      } else if (mutation == "scope") {
        auto call = first<func::CallOp>(function);
        call->setOperand(0, function.getArgument(0));
      } else if (mutation == "carry") {
        auto yield = cast<scf::YieldOp>(loop.getAfter().front().back());
        yield->setOperand(2, loop.getOperand(2));
      } else if (mutation == "extra action") {
        auto iteration = first<runtime::IterationOp>(function);
        OpBuilder builder(iteration);
        builder.clone(*iteration);
      } else if (mutation == "unreachable block") {
        OpBuilder builder(&context);
        auto *extra = builder.createBlock(&packet.getRegion());
        builder.setInsertionPointToEnd(extra);
        auto no =
            arith::ConstantIntOp::create(builder, function.getLoc(), 0, 1);
        scf::YieldOp::create(builder, function.getLoc(),
                             ValueRange{no, loop.getOperand(2)});
      } else
        loop->setAttr("unaccounted", UnitAttr::get(&context));
      require(succeeded(verify(*module)), "mutation must remain well formed");
      unsigned remaining = 10000;
      require(!read(function, remaining), "changed schedule accepted");
      sourceReturn(function);
      auto view = protocol::readScheduledExecutionClosure(*module);
      require(!view, "whole scheduled closure accepted changed semantics");
      llvm::consumeError(view.takeError());
    });
  for (StringRef mutation : {"missing cleanup", "duplicate cleanup",
                             "leaked owner", "borrowed result"})
    cases.run("SCF ownership refuses " + mutation, [&] {
      auto module = parse();
      auto function = module->lookupSymbol<func::FuncOp>("loop");
      auto release = first<runtime::ReleaseTransferOp>(function);
      OpBuilder builder(release);
      if (mutation == "missing cleanup") {
        runtime::ReleaseTransferOp cleanup;
        function.walk([&](runtime::ReleaseTransferOp op) {
          if (op->getBlock()->getNumArguments() == 1 &&
              isa<exec::StopType>(op->getBlock()->getArgument(0).getType()))
            cleanup = op;
        });
        require(bool(cleanup), "missing failure cleanup");
        cleanup.erase();
      } else if (mutation == "duplicate cleanup")
        builder.clone(*release);
      else if (mutation == "leaked owner") {
        auto initial = first<runtime::BorrowTransferOp>(function);
        builder.clone(*initial);
      } else {
        builder.setInsertionPointToStart(&function.front());
        auto scope = function.getArgument(0);
        auto packet = scf::ExecuteRegionOp::create(builder, function.getLoc(),
                                                   TypeRange{scope.getType()});
        builder.createBlock(&packet.getRegion());
        scf::YieldOp::create(builder, function.getLoc(), ValueRange{scope});
      }
      require(succeeded(verify(*module)), "ownership mutation is malformed");
      ScopedDiagnosticHandler quiet(&context,
                                    [](Diagnostic &) { return success(); });
      require(failed(runtime::verifyScheduledScopeOwnership(function)),
              "invalid SCF ownership accepted");
    });
  cases.run(
      "nested schedule depth is bounded before recursive verification", [&] {
        auto module = parse();
        auto function = module->lookupSymbol<func::FuncOp>("loop");
        OpBuilder builder(&context);
        builder.setInsertionPointToStart(&function.front());
        for (unsigned i = 0; i < 70; ++i) {
          auto packet = scf::ExecuteRegionOp::create(builder, function.getLoc(),
                                                     TypeRange{});
          auto *block = builder.createBlock(&packet.getRegion());
          scf::YieldOp::create(builder, function.getLoc());
          builder.setInsertionPointToStart(block);
        }
        ScopedDiagnosticHandler quiet(&context,
                                      [](Diagnostic &) { return success(); });
        require(failed(runtime::verifyScheduledScopeOwnership(function)),
                "ownership inspection has no structural depth bound");
        auto view = protocol::readScheduledExecutionClosure(*module);
        require(!view, "closure inspection accepted excessive nesting");
        llvm::consumeError(view.takeError());
      });
  return cases.result();
}
