#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/AnalysisManager.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/MathematicalFacts.h"
#include "zkc/Dialect/IR.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
constexpr const char *program = R"mlir(
!S = !data.sequence<i1>
module {
 func.func private @append(%s:!S,%flag:i1)->!S {
   %next = "data.sequence_append"(%s,%flag) : (!S,i1)->!S
   func.return %next : !S
 }
 func.func @subject(%flag:i1)->!S {
   %empty = "data.sequence_empty"() : ()->!S
   %a = func.call @append(%empty,%flag) : (!S,i1)->!S
   %b = func.call @append(%a,%flag) : (!S,i1)->!S
   func.return %b : !S
 }
})mlir";
void expectExtent(MathematicalFactAnalysis &analysis, Value value,
                  uint64_t expected, facts::Work &work) {
  auto result = analysis.extent(value, 0, work);
  require(result.status == facts::Status::Proven &&
              result.value == std::optional<uint64_t>(expected),
          "unexpected extent under current helper body");
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run("module analysis invalidates after sibling helper mutation", [&] {
    auto module = parseSourceString<ModuleOp>(program, &context);
    require(bool(module) && succeeded(verify(*module)), "fixture refused");
    auto subject = module->lookupSymbol<func::FuncOp>("subject");
    Value result = subject.front().back().getOperand(0);
    ModuleAnalysisManager storage(*module, nullptr);
    AnalysisManager manager = storage;
    auto &before = manager.getAnalysis<MathematicalFactAnalysis>();
    require(before.getRoot() == module->getOperation(), "wrong closure owner");
    uint64_t allowance = 65536;
    facts::Work work(allowance);
    expectExtent(before, result, 2, work);
    require(manager.getCachedAnalysis<MathematicalFactAnalysis>().has_value(),
            "analysis not cached at module owner");

    auto helper = module->lookupSymbol<func::FuncOp>("append");
    helper.front().back().setOperand(0, helper.getArgument(0));
    require(succeeded(verify(*module)), "changed helper refused");
    // A pass that changes an inspected sibling must not preserve this analysis.
    manager.invalidate(AnalysisManager::PreservedAnalyses{});
    require(!manager.getCachedAnalysis<MathematicalFactAnalysis>(),
            "stale helper observations survived invalidation");
    auto &after = manager.getAnalysis<MathematicalFactAnalysis>();
    expectExtent(after, result, 0, work);
  });
  cases.run("derived facts invalidate when their symbol dependency does", [&] {
    auto module = parseSourceString<ModuleOp>(program, &context);
    require(bool(module), "fixture refused");
    ModuleAnalysisManager storage(*module, nullptr);
    AnalysisManager manager = storage;
    auto value =
        module->lookupSymbol<func::FuncOp>("subject").front().back().getOperand(
            0);
    uint64_t remaining = 65536;
    facts::Work work(remaining);
    expectExtent(manager.getAnalysis<MathematicalFactAnalysis>(), value, 2,
                 work);
    require(manager.getCachedAnalysis<SymbolClosureAnalysis>().has_value(),
            "fact extraction did not record its dependency");
    AnalysisManager::PreservedAnalyses both;
    both.preserve<MathematicalFactAnalysis>();
    both.preserve<SymbolClosureAnalysis>();
    manager.invalidate(both);
    require(manager.getCachedAnalysis<MathematicalFactAnalysis>().has_value(),
            "unchanged dependencies lost reusable facts");
    auto helper = module->lookupSymbol<func::FuncOp>("append");
    helper.front().back().setOperand(0, helper.getArgument(0));
    AnalysisManager::PreservedAnalyses derivedOnly;
    derivedOnly.preserve<MathematicalFactAnalysis>();
    manager.invalidate(derivedOnly);
    require(!manager.getCachedAnalysis<MathematicalFactAnalysis>(),
            "preserving a derived result hid its invalidated dependency");
    expectExtent(manager.getAnalysis<MathematicalFactAnalysis>(), value, 0,
                 work);
  });
  cases.run("candidate clone and query work are independent subjects", [&] {
    auto module = parseSourceString<ModuleOp>(program, &context);
    require(bool(module) && succeeded(verify(*module)), "fixture refused");
    OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(module->clone()));
    auto result =
        module->lookupSymbol<func::FuncOp>("subject").front().back().getOperand(
            0);
    auto other = candidate->lookupSymbol<func::FuncOp>("subject")
                     .front()
                     .back()
                     .getOperand(0);
    MathematicalFactAnalysis analysis(*module);
    uint64_t empty = 0;
    facts::Work exhausted(empty);
    require(analysis.extent(result, 0, exhausted).status ==
                facts::Status::Capacity,
            "capacity became evidence or ordinary absence");
    uint64_t allowance = 65536;
    facts::Work work(allowance);
    expectExtent(analysis, result, 2, work);
    require(analysis.extent(other, 0, work).status == facts::Status::Unknown,
            "source analysis accepted a cloned subject");
    MathematicalFactAnalysis candidateAnalysis(*candidate);
    expectExtent(candidateAnalysis, other, 2, work);
    auto helper = candidate->lookupSymbol<func::FuncOp>("append");
    helper.front().back().setOperand(0, helper.getArgument(0));
    candidateAnalysis.clear();
    expectExtent(candidateAnalysis, other, 0, work);
    expectExtent(analysis, result, 2, work);
  });
  return cases.result();
}
