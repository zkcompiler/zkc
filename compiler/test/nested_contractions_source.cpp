#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "support/ScopedFinite.h"
#include "zkc/Analysis/Computation.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/NativeLanguage.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Algorithms.h"
#include <fstream>
#include <sstream>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace sf = zkc::test::scopedFinite;
namespace {
std::string fixture(bool mathematics = true) {
  std::ifstream stream(ZKC_NESTED_SOURCE);
  require(bool(stream), "missing nested source fixture");
  std::ostringstream result;
  result << stream.rdbuf();
  auto text = result.str();
  if (!mathematics)
    return text;
  const std::string expression = "s+a*b";
  text.replace(text.find(expression), expression.size(), "s+multiply(a,b)");
  text += "\nmath fn product(a:F,b:F)->F { return a*b; }\n"
          "math fn multiply(a:F,b:F)->F { return product(a,b); }\n";
  return text;
}
std::string replace(std::string text, StringRef from, StringRef to) {
  size_t position = 0;
  require(text.find(from.str()) != std::string::npos, "missing fixture edit");
  while ((position = text.find(from.str(), position)) != std::string::npos) {
    text.replace(position, from.size(), to.str());
    position += to.size();
  }
  return text;
}
OwningOpRef<ModuleOp> prepareSource(MLIRContext &context) {
  auto captured = take(
      language::capture({{"sample", fixture(), "nested-read-through.zkc"}}));
  auto checked = take(language::analyze(captured).checkedProject());
  auto entry = take(closeProtocolDeployment(checked, "sample::Demo"));
  auto original = take(language::prepareOriginal(entry));
  auto source = parseSourceString<ModuleOp>(original.bytes(), &context);
  require(bool(source), "source read-through fixture refused");
  auto result = protocol::expandScopedHelpers(*source);
  require(bool(result), "source helper expansion failed");
  return result;
}
Operation *product(ModuleOp module) {
  Operation *result = nullptr;
  module.walk([&](Operation *op) {
    auto *meaning = finite::semantics(op);
    if (!result && op->getParentOfType<mlir::ModuleOp>() && meaning &&
        meaning->identity == MathematicalIdentity::FieldMultiply)
      result = op;
  });
  require(result, "missing retained raw multiplication");
  return result;
}
OwnedComputation outerCollection(ModuleOp module) {
  return sf::computation(module);
}
unsigned matvecs(ModuleOp module) {
  protocol_ir::LocalCallOp root;
  module.walk([&](protocol_ir::LocalCallOp call) { root = call; });
  require(bool(root), "missing protocol-root invocation");
  return sf::executionApplications(module, root.getCallee(),
                                   "matrix.mul_vector")
             .size() +
         sf::executionApplications(module, root.getCallee(),
                                   "matrix.transpose_mul_vector")
             .size();
}
// Return a scalar through a nonzero result coordinate and retain another exact
// coordinate. No numerical normalization or additional scalar work is involved.
func::CallOp outlineProduct(Operation *operation) {
  auto *unit = operation->getParentOfType<func::FuncOp>()->getParentOp();
  OpBuilder builder(unit->getContext());
  builder.setInsertionPointToEnd(&unit->getRegion(0).front());
  Type field = operation->getResult(0).getType();
  auto helper = func::FuncOp::create(
      builder, operation->getLoc(), "coordinate_helper",
      builder.getFunctionType({field, field}, {field, field}));
  helper.setPrivate();
  auto *body = helper.addEntryBlock();
  builder.setInsertionPointToEnd(body);
  IRMapping mapping;
  mapping.map(operation->getOperands(), body->getArguments());
  auto *copied = builder.clone(*operation, mapping);
  func::ReturnOp::create(
      builder, operation->getLoc(),
      ValueRange{body->getArgument(0), copied->getResult(0)});
  builder.setInsertionPoint(operation);
  auto call = func::CallOp::create(builder, operation->getLoc(), helper,
                                   operation->getOperands());
  operation->getResult(0).replaceAllUsesWith(call.getResult(1));
  operation->erase();
  return call;
}
void inlineMathHelpers(ModuleOp module) {
  unsigned remaining = 10000;
  module.walk([&](func::FuncOp function) {
    if (protocol::isScopedExecutionFunction(function))
      return;
    for (auto iterator = function.front().begin();
         iterator != function.front().end();) {
      auto call = dyn_cast<func::CallOp>(&*iterator++);
      if (!call)
        continue;
      require(remaining--, "test helper substitution exceeded its bound");
      auto helper = SymbolTable::lookupNearestSymbolFrom<func::FuncOp>(
          call, call.getCalleeAttr());
      require(helper && helper.getBody().hasOneBlock(), "missing raw helper");
      IRMapping values;
      values.map(helper.getArguments(), call.getOperands());
      OpBuilder builder(call);
      Operation *first = nullptr;
      for (auto &op : helper.front().without_terminator()) {
        auto *copy = builder.clone(op, values);
        if (!first)
          first = copy;
      }
      for (auto [result, returned] :
           llvm::zip(call.getResults(), helper.front().back().getOperands()))
        result.replaceAllUsesWith(values.lookup(returned));
      call.erase();
      if (first)
        iterator = first->getIterator();
    }
  });
}
void routeOuterInputs(ModuleOp module) {
  auto computation = outerCollection(module);
  auto helper = cast<func::FuncOp>(computation.helper);
  exec::FoldOp inner;
  helper.walk([&](exec::FoldOp call) { inner = call; });
  require(bool(inner), "missing nested call for input routing");
  OpBuilder builder(helper);
  SmallVector<Type> types(inner.getInputs().getTypes());
  auto entry = func::FuncOp::create(builder, helper.getLoc(), "routing",
                                    builder.getFunctionType(types, types));
  entry.setPrivate();
  builder.setInsertionPointToEnd(entry.addEntryBlock());
  func::ReturnOp::create(builder, helper.getLoc(), entry.getArguments());
  auto stop = cast<exec::DispatchOp>(inner->getNextNode()).getStopped();
  IRRewriter rewriter(module.getContext());
  auto *before = inner->getBlock();
  auto *tail = rewriter.splitBlock(before, inner->getIterator());
  builder.setInsertionPointToEnd(before);
  exec::ScopedExecutionBuilder control(builder, helper);
  auto outputs = control.invoke(
      "exec.compute", types, control.scoped(inner.getInputs()),
      {builder.getNamedAttr("callee",
                            FlatSymbolRefAttr::get(entry.getSymNameAttr())),
       builder.getNamedAttr("site", builder.getStringAttr("routing"))},
      stop);
  inner.getInputsMutable().assign(outputs);
  rewriter.mergeBlocks(tail, builder.getInsertionBlock());
}
void pinCallbackResult(ModuleOp module) {
  auto computation = outerCollection(module);
  auto view = finite::analyzeComputation(computation);
  require(view && view->nested.size() == 1, "missing nested callback");
  auto helper = cast<func::FuncOp>(view->nested.front().computation.helper);
  auto add = sf::application(helper, "field.add");
  auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
      add, add.getBindingAttr());
  auto original = take(protocol::readBinding(binding));
  auto selected = protocol::defaultImplementation(original.application);
  require(bool(selected), "missing pinned field implementation");
  binding.setImplementation(*selected);
}
void refusesSource(ModuleOp source, ModuleOp candidate) {
  // Synchronize the actual plain helper definitions so dependency inequality
  // cannot alone reject a stale strategy. The checker still has to reread
  // the changed callback operands, scalar work and returned coordinates.
  auto stale = sf::clone(candidate);
  auto *owner = &stale->getBody()->front();
  for (auto &operation : source.getBody()->front().getRegion(0).front()) {
    auto helper = dyn_cast<func::FuncOp>(operation);
    if (!helper || protocol::isScopedExecutionFunction(helper))
      continue;
    auto *previous = SymbolTable::lookupSymbolIn(owner, helper.getSymName());
    OpBuilder builder(source.getContext());
    if (previous)
      builder.setInsertionPoint(previous);
    else
      builder.setInsertionPointToEnd(&owner->getRegion(0).front());
    builder.clone(operation);
    if (previous)
      previous->erase();
  }
  require(succeeded(verify(source)), "source mutation was not admitted");
  require(succeeded(verify(*stale)), "stale candidate was not admitted");
  bool named = false;
  ScopedDiagnosticHandler quiet(
      source.getContext(), [&](Diagnostic &diagnostic) {
        for (const auto &refusal : diagnostics::refusals(diagnostic))
          named |= refusal.code == "algorithm-correspondence";
        return success();
      });
  require(failed(sf::compare(source, *stale)) && named,
          "independent reader accepted changed actual source");
}

} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  for (bool mathematics : {false, true})
    for (bool columns : {false, true})
      for (StringRef seed : {"seed", "0", "19"})
        cases.run(
            llvm::Twine(mathematics ? "retained " : "direct ") +
                (columns ? "columns " : "rows ") + seed,
            [&] {
              auto text = replace(fixture(mathematics), ",seed,fn",
                                  ("," + seed + ",fn").str());
              if (columns)
                text = replace(replace(text, "indices.rows", "indices.columns"),
                               "matrix.row", "matrix.column");
              auto captured = take(
                  language::capture({{"sample", text, "nested-matrix.zkc"}}));
              auto checked = take(language::analyze(captured).checkedProject());
              auto entry =
                  take(closeProtocolDeployment(checked, "sample::Demo"));
              auto original = take(language::prepareOriginal(entry));
              auto source =
                  parseSourceString<ModuleOp>(original.bytes(), &context);
              require(bool(source), "original source IR refused");
              auto expanded = protocol::expandScopedHelpers(*source);
              require(bool(expanded), "scoped helper expansion failed");
              unsigned retained = 0, rawCalls = 0;
              expanded->walk([&](exec::ComputeOp) { ++retained; });
              expanded->walk([&](func::CallOp call) {
                rawCalls += !protocol::isScopedExecutionFunction(
                    call->getParentOfType<func::FuncOp>());
              });
              require(!mathematics || (retained && rawCalls),
                      "test no longer exercises retained helper mathematics");
              auto candidate = sf::prepare(*expanded);

              require(succeeded(sf::compare(*expanded, *candidate)),
                      "nested source correspondence failed");
              // Other independently admitted callback declarations can contain
              // ordered loops; the root collection must choose the bulk
              // strategy.
              require(matvecs(*candidate) == 1,
                      "source spelling missed whole collection strategy: " +
                          Twine(matvecs(*candidate)));
              take(language::compileEntry(original));
              take(language::compileEntry(original, {false, false}));
            });
  for (bool routing : {false, true})
    cases.run(
        routing ? "pure helper result input routing"
                : "direct mathematical helper body",
        [&] {
          auto source = prepareSource(context);
          if (routing)
            routeOuterInputs(*source);
          else
            inlineMathHelpers(*source);
          require(succeeded(verify(*source)), "changed helper source refused");
          auto candidate = sf::prepare(*source);
          require(matvecs(*candidate) == 1 &&
                      succeeded(sf::compare(*source, *candidate)),
                  "exact helper substitution missed checked matrix strategy");
        });
  cases.run("exact helper substitution and source return coordinates", [&] {
    auto source = prepareSource(context);
    auto call = outlineProduct(product(*source));
    require(succeeded(verify(*source)), "outlined raw source refused");
    auto computation = outerCollection(*source);
    auto view = finite::analyzeComputation(computation);
    require(view && view->nested.size() == 1 &&
                view->nested.front().numericalBody,
            "nested owned numerical body was not read through");
    finite::ComputationWork measured;
    require(bool(finite::analyzeComputation(computation, measured)),
            "bounded read-through failed with its normal allowance");
    finite::ComputationWork bounded;
    bounded.structural -= measured.structural + 1;
    finite::ComputationDiagnostic diagnostic;
    require(!finite::analyzeComputation(computation, bounded, &diagnostic) &&
                diagnostic.outcome.status == OptimizationStatus::Capacity &&
                diagnostic.outcome.capacity &&
                diagnostic.outcome.capacity->owner == WorkOwner::Structural &&
                diagnostic.subject == computation.operation,
            "read-through exhausted work without a safe source diagnostic");
    auto &inner = view->nested.front();
    for (const auto &output : inner.resultMappings)
      require(output.yielded == inner.callbackValue(output.sourceYielded),
              "callback return coordinate lost exact SSA substitution");
    require(view->sourceOperation(inner.occurrence) != inner.occurrence,
            "temporary nested call has no original source instruction");
    auto candidate = sf::prepare(*source);
    require(matvecs(*candidate) == 1 &&
                succeeded(sf::compare(*source, *candidate)),
            "independent reader lost exact result coordinate");
    auto helper = SymbolTable::lookupNearestSymbolFrom<func::FuncOp>(
        call, call.getCalleeAttr());
    auto &returned = helper.front().back();
    require(returned.getNumOperands() == 2, "missing multi-result return");
    Value first = returned.getOperand(0);
    returned.setOperand(0, returned.getOperand(1));
    returned.setOperand(1, first);
    refusesSource(*source, *candidate);
  });
  for (StringRef change :
       {"dead arithmetic", "dead helper invocation", "actual operand",
        "compute operand", "policy", "implementation pin"})
    cases.run("retained source refusal: " + change, [&] {
      auto source = prepareSource(context);
      auto candidate = sf::prepare(*source);
      require(matvecs(*candidate) == 1, "missing positive bulk candidate");
      if (change == "dead arithmetic") {
        OpBuilder builder(product(*source));
        builder.clone(*product(*source));
      } else if (change == "dead helper invocation") {
        auto call = outlineProduct(product(*source));
        OpBuilder builder(call);
        builder.clone(*call);
      } else if (change == "actual operand") {
        auto *operation = product(*source);
        operation->setOperand(1, operation->getOperand(0));
      } else if (change == "compute operand") {
        auto computation = outerCollection(*source);
        auto view = finite::analyzeComputation(computation);
        require(view && view->nested.size() == 1, "missing source step");
        auto helper =
            cast<func::FuncOp>(view->nested.front().computation.helper);
        bool changed = false;
        helper.walk([&](exec::ComputeOp call) {
          for (auto &operand : call->getOpOperands())
            if (!changed && operand.get() == helper.getArgument(2)) {
              operand.set(helper.getArgument(1));
              changed = true;
            }
        });
        require(changed, "missing item at mathematical invocation boundary");
      } else if (change == "implementation pin") {
        pinCallbackResult(*source);
      } else {
        source->walk([&](exec::ComputeOp call) {
          Builder builder(&context);
          call->setAttr("policy",
                        builder.getBoolArrayAttr({false, true, false}));
        });
      }
      refusesSource(*source, *candidate);
      auto fallback = sf::prepare(*source);
      require(matvecs(*fallback) == 0 && sf::hasLoop(*fallback) &&
                  succeeded(sf::compare(*source, *fallback)),
              "unsupported retained payload lost checked ordered fallback");
    });
  cases.run("effectful callback keeps ordered fallback", [&] {
    auto text = replace(fixture(), "=>s+multiply(a,b)",
                        "=>{require true;s+multiply(a,b)}");
    auto captured =
        take(language::capture({{"sample", text, "nested-effect.zkc"}}));
    auto checked = take(language::analyze(captured).checkedProject());
    auto entry = take(closeProtocolDeployment(checked, "sample::Demo"));
    auto original = take(language::prepareOriginal(entry));
    auto source = parseSourceString<ModuleOp>(original.bytes(), &context);
    require(bool(source), "effectful source refused");
    auto expanded = protocol::expandScopedHelpers(*source);
    require(bool(expanded), "effectful helper expansion failed");
    auto candidate = sf::prepare(*expanded);
    require(matvecs(*candidate) == 0 && sf::hasLoop(*candidate) &&
                succeeded(sf::compare(*expanded, *candidate)),
            "effectful source was replaced by bulk work");
    take(language::compileEntry(original));
  });
  return cases.result();
}
