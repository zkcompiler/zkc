#include "../lib/Transforms/ScopedCandidate.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/Parser/Parser.h"
#include "support/ScopedFinite.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Algorithms.h"
#include <fstream>
#include <sstream>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
using namespace zkc::test::scopedFinite;
namespace {
std::string fixture() {
  std::ifstream input(std::string(ZKC_FINITE_FIXTURES) + "/nested-matrix.mlir");
  require(bool(input), "missing nested matrix fixture");
  std::ostringstream result;
  result << input.rdbuf();
  return result.str();
}
exec::TestOp branch(ModuleOp module) {
  exec::TestOp result;
  function(module, "work").walk([&](exec::TestOp operation) {
    result = operation;
  });
  require(bool(result), "missing outer nonempty branch");
  return result;
}
func::FuncOp nonempty(ModuleOp module) {
  auto bulk = applications(module, "matrix.mul_vector");
  if (bulk.empty())
    bulk = applications(module, "matrix.transpose_mul_vector");
  require(bulk.size() == 1, "expected one nested matrix strategy");
  return bulk.front()->getParentOfType<func::FuncOp>();
}
void eraseInvocation(exec::ApplyOp operation) {
  auto dispatch = cast<exec::DispatchOp>(operation->getNextNode());
  auto *next = dispatch.getReturned();
  for (auto argument : next->getArguments())
    require(argument.use_empty(), "cannot erase a live invocation payload");
  while (next->getNumArguments())
    next->eraseArgument(0);
  auto *before = operation->getBlock();
  dispatch.erase();
  operation.erase();
  IRRewriter rewriter(before->getParentOp()->getContext());
  rewriter.mergeBlocks(next, before);
}
void checkStructure(ModuleOp source, ModuleOp candidate, bool columns) {
  auto closure =
      take(protocol::readSourceExecutionClosure(&candidate.getBody()->front()));
  auto selected = nonempty(candidate);
  auto view =
      take(mathematical::ScopedCandidate::read(&candidate.getBody()->front()));
  auto *control = view->get(branch(candidate));
  require(control && control->regions.size() == 2 &&
              control->regions[0] == selected,
          "matvec was speculated outside the entered nonempty arm");
  require(applications(selected, columns ? "matrix.transpose_mul_vector"
                                         : "matrix.mul_vector")
                      .size() == 1 &&
              !hasLoop(selected) &&
              applications(selected, "matrix.row_dot").empty() &&
              applications(selected, "matrix.column_dot").empty(),
          "whole collection retained scalar iteration or wrong orientation");
  auto empty = control->regions[1];
  unsigned operations = 0;
  empty.walk([&](exec::ApplyOp operation) {
    ++operations;
    require(contract(operation) == "vector.empty",
            "empty outer executes inner admission");
  });
  require(operations == 1 && !hasLoop(empty),
          "empty arm lost its exact result");
  unsigned requests = 0;
  candidate.walk([&](Operation *op) {
    requests += isa<exec::FoldOp, exec::CollectOp>(op);
  });
  require(!requests, "finite preparation left unresolved requests");
  require(succeeded(compare(source, candidate)),
          "independent scoped collection comparison failed");
}
void hoistAdmission(ModuleOp module) {
  auto owner = nonempty(module);
  auto index =
      take(mathematical::ScopedCandidate::read(&module.getBody()->front()));
  auto test = branch(module);
  auto *selected = index->get(test);
  auto *first = index->first(&owner.front());
  SmallVector<Operation *> prefix;
  for (unsigned i = 0; i != 3; ++i) {
    require(first && isa<exec::ApplyOp>(first), "missing inner guard prefix");
    prefix.push_back(first);
    first = index->next(first);
  }
  require(contract(cast<exec::ApplyOp>(prefix.back())) == "control.require",
          "unexpected selected-row guard prefix");
  IRMapping values;
  values.map(owner.getArguments().drop_front(),
             ValueRange(selected->inputs).drop_front());
  auto caller = test->getParentOfType<func::FuncOp>();
  auto stop = cast<exec::DispatchOp>(test->getNextNode()).getStopped();
  IRRewriter rewriter(module.getContext());
  auto *before = test->getBlock();
  auto *tail = rewriter.splitBlock(before, test->getIterator());
  OpBuilder builder(module.getContext());
  builder.setInsertionPointToEnd(before);
  exec::ScopedExecutionBuilder control(builder, caller);
  for (auto *operation : prefix) {
    auto *step = index->get(operation);
    SmallVector<Value> inputs;
    for (Value value : step->inputs)
      inputs.push_back(values.lookup(value));
    auto outputs =
        control.invoke("exec.apply", ValueRange(step->outputs).getTypes(),
                       control.scoped(inputs), operation->getAttrs(), stop);
    values.map(step->outputs, outputs);
  }
  rewriter.mergeBlocks(tail, builder.getInsertionBlock());
  for (auto *operation : llvm::reverse(prefix))
    eraseInvocation(cast<exec::ApplyOp>(operation));
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  auto source = parseSourceString<ModuleOp>(fixture(), &context);
  require(bool(source), "source fixture refused");
  for (bool columns : {false, true})
    cases.run(columns ? "all columns" : "all rows", [&] {
      auto original = clone(*source);
      if (columns) {
        original->walk([&](data::DomainIndicesOp op) { op.setAxis(1); });
        SmallVector<data::DomainMatrixRowOp> rows;
        original->walk([&](data::DomainMatrixRowOp op) { rows.push_back(op); });
        for (auto row : rows) {
          OpBuilder builder(row);
          OperationState state(row.getLoc(),
                               data::DomainMatrixColumnOp::getOperationName());
          state.addOperands(row->getOperands());
          state.addTypes(row->getResultTypes());
          auto *replacement = builder.create(state);
          row->getResult(0).replaceAllUsesWith(replacement->getResult(0));
          row.erase();
        }
      }
      auto candidate = prepare(*original);
      checkStructure(*original, *candidate, columns);
    });
  cases.run("disabled family keeps checked ordered execution", [&] {
    auto candidate = prepare(*source, {false, false});
    require(applications(*candidate, "matrix.mul_vector").empty() &&
                hasLoop(*candidate) && succeeded(compare(*source, *candidate)),
            "disabled selection lost the source or selected bulk work");
  });
  auto accepted = prepare(*source);
  auto mutation = [&](StringRef name, llvm::function_ref<void(ModuleOp)> edit) {
    cases.run("candidate refuses " + name, [&] {
      auto candidate = clone(*accepted);
      edit(*candidate);
      require(succeeded(verify(*candidate)), "mutation must retain formed IR");
      bool named = false;
      ScopedDiagnosticHandler quiet(&context, [&](Diagnostic &diagnostic) {
        for (const auto &refusal : diagnostics::refusals(diagnostic))
          named |= refusal.code == "algorithm-correspondence";
        return success();
      });
      require(failed(compare(*source, *candidate)) && named,
              "changed scoped candidate acquired correspondence");
    });
  };
  mutation("wrong branch capture", [&](ModuleOp module) {
    auto work = function(module, "work");
    unsigned entries = 0, calls = 0;
    work.walk([&](runtime::EnterScopeOp enter) {
      if (enter.getKind() == "conditional") {
        enter.getInputsMutable()[0].set(work.getArgument(4));
        enter.getInputsMutable()[3].set(work.getArgument(1));
        ++entries;
      }
    });
    work.walk([&](func::CallOp call) {
      call->setOperand(1, work.getArgument(4));
      call->setOperand(4, work.getArgument(1));
      ++calls;
    });
    require(entries == 2 && calls == 2, "missing paired conditional captures");
  });
  mutation("outer dimension orientation", [&](ModuleOp module) {
    auto operation = application(function(module, "work"), "matrix.dimension");
    operation.setParametersAttr(Builder(&context).getStrArrayAttr({"1"}));
  });
  mutation("strict zip guard order", [&](ModuleOp module) {
    auto comparisons = applications(nonempty(module), "index.equal");
    require(comparisons.size() == 2, "missing independent strict zip checks");
    Value first = comparisons[0].getInputs()[1];
    comparisons[0]->setOperand(2, comparisons[1].getInputs()[1]);
    comparisons[1]->setOperand(2, first);
  });
  mutation("inner admission before empty branch", hoistAdmission);
  mutation("surrounding helper return", [&](ModuleOp module) {
    auto step = function(module, "step");
    step.walk([&](exec::ReturnOp operation) {
      operation->setOperand(0, step.getArgument(1));
    });
  });
  mutation("surrounding domain mapping", [&](ModuleOp module) {
    auto domain = SymbolTable(&module.getBody()->front())
                      .lookup<data::DomainOp>("inner_domain");
    require(bool(domain), "missing surrounding domain");
    domain.walk([&](data::DomainElementsOp operation) {
      operation->setOperand(0, domain.getBody().front().getArgument(3));
    });
  });
  for (StringRef implementation : {"field.add", "field.mul"})
    cases.run("explicit implementation fallback " + implementation, [&] {
      auto original = clone(*source);
      auto operation = application(*original, implementation);
      auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
          operation, operation.getBindingAttr());
      auto info = take(protocol::readBinding(binding));
      auto selected = protocol::defaultImplementation(info.application);
      require(bool(selected), "missing native implementation");
      binding.setImplementation(*selected);
      auto candidate = prepare(*original);
      require(applications(*candidate, "matrix.mul_vector").empty() &&
                  hasLoop(*candidate) &&
                  succeeded(compare(*original, *candidate)),
              "explicit scalar binding was replaced by bulk work");
    });
  cases.run("opaque callback keeps ordered execution", [&] {
    auto original = clone(*source);
    auto step = function(*original, "step");
    step.walk([&](exec::ReturnOp operation) {
      operation->setOperand(0, step.getArgument(1));
    });
    auto candidate = prepare(*original);
    require(applications(*candidate, "matrix.mul_vector").empty() &&
                hasLoop(*candidate) &&
                succeeded(compare(*original, *candidate)),
            "unsupported callback was replaced");
  });
  cases.run("shared callback lifetime across two collections", [&] {
    auto original = clone(*source);
    auto first = function(*original, "work");
    auto second = cast<func::FuncOp>(first->clone());
    second.setSymName("second_collection");
    first->getBlock()->getOperations().insert(first->getIterator(), second);
    auto candidate = prepare(*original);
    require(applications(*candidate, "matrix.mul_vector").size() == 2 &&
                succeeded(compare(*original, *candidate)),
            "two collections lost their shared callback ownership");
  });
  for (bool copyBudget : {false, true})
    cases.run(
        copyBudget ? "copy refusal preserves source"
                   : "origin refusal preserves source",
        [&] {
          auto before = clone(*source);
          mathematical::RealizationWork work;
          uint64_t copy = copyBudget ? 0 : 1000000;
          uint64_t bytes = copyBudget ? 16 * 1024 * 1024 : 0;
          std::optional<CapacityCause> capacity;
          auto refused = protocol::prepareScopedFinite(*source, work, copy,
                                                       bytes, capacity);
          require(!refused && capacity &&
                      capacity->owner ==
                          (copyBudget ? WorkOwner::AlgorithmExpansion
                                      : WorkOwner::AlgorithmOriginBytes) &&
                      OperationEquivalence::isEquivalentTo(
                          *before, *source, OperationEquivalence::Flags{}),
                  "required construction refusal published source mutation");
        });
  for (bool hashed : {false, true})
    cases.run(
        hashed ? "hashed guard survives helper expansion"
               : "guard survives helper expansion",
        [&] {
          auto original = clone(*source);
          auto body = function(*original, "body");
          auto fold = cast<exec::FoldOp>(body.front().front());
          fold.setSite(hashed ? std::string(120, 'i') : "inner");
          auto location =
              FileLineColLoc::get(&context, "inner-fold.zkc", 17, 3);
          fold->setLoc(location);
          auto selected = prepare(*original);
          auto expanded = protocol::expandScopedHelpers(*selected);
          require(bool(expanded) &&
                      succeeded(protocol::verifyScopedHelperExpansionPreserved(
                          *selected, *expanded)),
                  "helper expansion lost selected nested source");
          auto guards = applications(nonempty(*expanded), "control.require");
          require(guards.size() == 3, "missing expanded admission guards");
          for (auto guard : guards)
            require(guard->getLoc() == location,
                    "helper expansion lost guard location");
          guards.front()->setLoc(
              FileLineColLoc::get(&context, "wrong-fold.zkc", 1, 1));
          require(failed(protocol::verifyScopedHelperExpansionPreserved(
                      *selected, *expanded)),
                  "helper expansion accepted changed guard location");
          guards.front()->setLoc(location);
          guards.front().setSite("changed_guard");
          require(failed(protocol::verifyScopedHelperExpansionPreserved(
                      *selected, *expanded)),
                  "helper expansion accepted changed guard identity");
        });
  return cases.result();
}
