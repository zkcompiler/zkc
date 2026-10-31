#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Interfaces/ControlFlowInterfaces.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Transforms/GreedyPatternRewriteDriver.h"
#include "mlir/Transforms/Passes.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Registry.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
constexpr StringLiteral matching = R"mlir(
!V = !data.variant<#data.identity<["atom", "Choice"]>, [#data.alternative<"left">, #data.alternative<"right">]>
!R = !exec.outcome<(ui64)>
module {
  func.func @choose(%scope: !runtime.scope, %value: !V, %capture: ui64) -> !R {
    "exec.match"(%scope, %value, %capture, %capture)[^failed, ^left, ^right]
      {alternatives=["left", "right"], site="choose", successor_operand_segments=array<i32: 0, 1, 1>} : (!runtime.scope, !V, ui64, ui64) -> ()
  ^left(%unused: ui64):
    %zero = "data.index"() {value=0 : ui64} : () -> ui64
    %l = "exec.returned"(%zero) : (ui64) -> !R
    func.return %l : !R
  ^right(%used: ui64):
    %r = "exec.returned"(%used) : (ui64) -> !R
    func.return %r : !R
  ^failed(%stop: !exec.stop):
    %f = "exec.failed"(%stop) : (!exec.stop) -> !R
    func.return %f : !R
  }
})mlir";
constexpr StringLiteral logicalMatching = R"mlir(
#choice = #data.layout<"variant", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "Choice", false, true, true, true alternatives [#data.layout_alternative<"left">, #data.layout_alternative<"right">]>
!V = !data.value<#choice>
module {
  func.func @choose(%value: !V, %capture: ui64) -> ui64 {
    "data.match"(%value, %capture, %capture)[^left, ^right]
      {alternatives=["left", "right"], successor_operand_segments=array<i32: 1, 1>} : (!V, ui64, ui64) -> ()
  ^left(%unused: ui64):
    %zero = "data.index"() {value=0 : ui64} : () -> ui64
    func.return %zero : ui64
  ^right(%used: ui64):
    func.return %used : ui64
  }
})mlir";
constexpr StringLiteral dispatching = R"mlir(
!R = !exec.outcome<(ui64)>
module {
  func.func @dispatch_pair(%cond: i1, %first: !R, %second: !R, %a: ui64, %b: ui64) -> !R {
    cf.cond_br %cond, ^one, ^two
  ^one:
    "exec.dispatch"(%first)[^returned_one, ^failed] : (!R) -> ()
  ^two:
    "exec.dispatch"(%second)[^returned_two, ^failed] : (!R) -> ()
  ^returned_one(%unused_a: ui64):
    %r1 = "exec.returned"(%a) : (ui64) -> !R
    func.return %r1 : !R
  ^returned_two(%unused_b: ui64):
    %r2 = "exec.returned"(%b) : (ui64) -> !R
    func.return %r2 : !R
  ^failed(%stop: !exec.stop):
    %f = "exec.failed"(%stop) : (!exec.stop) -> !R
    func.return %f : !R
  }
})mlir";
constexpr StringLiteral singleDispatch = R"mlir(
!R = !exec.outcome<(ui64)>
module {
  func.func @dispatch(%outcome: !R, %capture: ui64) -> !R {
    "exec.dispatch"(%outcome)[^returned, ^failed] : (!R) -> ()
  ^returned(%value: ui64):
    %r = "exec.returned"(%value) : (ui64) -> !R
    func.return %r : !R
  ^failed(%stop: !exec.stop):
    %f = "exec.failed"(%stop) : (!exec.stop) -> !R
    func.return %f : !R
  }
})mlir";
template <typename Op> Op first(ModuleOp module) {
  Op found;
  module.walk([&](Op op) {
    if (!found)
      found = op;
  });
  require(bool(found), "missing branch operation");
  return found;
}
template <typename Op> void mutateEdges(ModuleOp module) {
  auto op = first<Op>(module);
  auto branch = cast<BranchOpInterface>(op.getOperation());
  auto function = op->template getParentOfType<func::FuncOp>();
  Value value = function.getArguments().back();
  for (unsigned edge = 0; edge < op->getNumSuccessors(); ++edge) {
    SmallVector<SmallVector<Value>> before;
    for (unsigned i = 0; i < op->getNumSuccessors(); ++i)
      before.emplace_back(
          branch.getSuccessorOperands(i).getForwardedOperands());
    auto operands = branch.getSuccessorOperands(edge);
    auto produced = operands.getProducedOperandCount();
    unsigned oldSize = operands.size();
    operands.append(ValueRange{value});
    auto *block = op->getSuccessor(edge);
    block->addArgument(value.getType(), op.getLoc());
    require(succeeded(verify(module)), "edge append broke formation");
    for (unsigned i = 0; i < op->getNumSuccessors(); ++i)
      if (i != edge)
        require(branch.getSuccessorOperands(i).getForwardedOperands() ==
                    ValueRange(before[i]),
                "one edge mutation changed another edge");
    // Produced payload is determined by the input type, never by destination
    // arity. Even malformed IR must not relabel forwarded values as produced.
    block->addArgument(value.getType(), op.getLoc());
    require(branch.getSuccessorOperands(edge).getProducedOperandCount() ==
                    produced &&
                failed(verify(module)),
            "extra block argument became an invented produced value");
    block->eraseArgument(block->getNumArguments() - 1);
    branch.getSuccessorOperands(edge).erase(oldSize);
    block->eraseArgument(block->getNumArguments() - 1);
    require(succeeded(verify(module)), "edge erase broke formation");
  }
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  ScopedDiagnosticHandler quiet(&context,
                                [](Diagnostic &) { return success(); });
  auto parse = [&](StringRef text) {
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "branch fixture did not form");
    return module;
  };
  Cases cases;
  cases.run("exec match edges have independent mutable operands", [&] {
    auto module = parse(matching);
    mutateEdges<exec::MatchOp>(*module);
  });
  cases.run("logical match edges have independent mutable operands", [&] {
    auto module = parse(logicalMatching);
    mutateEdges<data::MatchOp>(*module);
  });
  cases.run("outcome and stop edges support standard operand mutation", [&] {
    auto module = parse(singleDispatch);
    mutateEdges<exec::DispatchOp>(*module);
  });
  for (auto text : {matching, logicalMatching, dispatching})
    for (auto level : {GreedySimplifyRegionLevel::Normal,
                       GreedySimplifyRegionLevel::Aggressive})
      cases.run("standard canonicalization preserves branch formation", [&] {
        auto module = parse(text);
        GreedyRewriteConfig config;
        config.setRegionSimplificationLevel(level);
        PassManager manager(&context);
        manager.addPass(createCanonicalizerPass(config));
        require(succeeded(manager.run(*module)) && succeeded(verify(*module)),
                "standard region simplification broke a branch interface");
        if (text == matching && level == GreedySimplifyRegionLevel::Normal) {
          auto op = first<exec::MatchOp>(*module);
          require(op.getForwarded()[1].empty() &&
                      op.getForwarded()[2].size() == 1,
                  "dead argument elimination changed the live edge");
        } else if (text == logicalMatching &&
                   level == GreedySimplifyRegionLevel::Normal) {
          auto op = first<data::MatchOp>(*module);
          require(op.getForwarded()[0].empty() &&
                      op.getForwarded()[1].size() == 1,
                  "logical match lost its independent live capture");
        }
      });
  const std::vector<std::vector<int32_t>> malformedSegments{
      {}, {-1, 1}, {0, 0, 0, 0}, {1000000}};
  for (auto text : {matching, logicalMatching})
    cases.run("match has no implicit shared-capture representation", [&] {
      auto module = parse(text);
      module->walk([&](Operation *op) {
        if (isa<exec::MatchOp, data::MatchOp>(op))
          op->removeAttr("successor_operand_segments");
      });
      require(failed(verify(*module)), "missing edge inventory accepted");
    });
  for (auto text : {matching, logicalMatching, dispatching})
    for (const auto &sizes : malformedSegments)
      cases.run("malformed successor segments refuse without crashing", [&] {
        auto module = parse(text);
        module->walk([&](Operation *op) {
          if (isa<exec::MatchOp, data::MatchOp, exec::DispatchOp>(op))
            op->setAttr("successor_operand_segments",
                        DenseI32ArrayAttr::get(&context, sizes));
        });
        require(failed(verify(*module)), "malformed branch segments accepted");
      });
  return cases.result();
}
