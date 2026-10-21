#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Analysis/Computation.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Kernel/IR/KernelOps.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/NestedContractions.h"
#include <fstream>
#include <sstream>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
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
struct Prepared {
  OwningOpRef<ModuleOp> module;
  protocol::AlgorithmExpansionState expansion;
};
Prepared prepare(MLIRContext &context) {
  auto captured = take(
      language::capture({{"sample", fixture(), "nested-read-through.zkc"}}));
  auto checked = take(language::analyze(captured).checkedProject());
  auto entry = take(closeProtocolDeployment(checked, "sample::Demo"));
  auto original = take(language::prepareOriginal(entry));
  Prepared result;
  result.module = parseSourceString<ModuleOp>(original.bytes(), &context);
  require(bool(result.module), "source read-through fixture refused");
  require(succeeded(mathematical::expandMathRealizations(*result.module)),
          "Kernel formation failed");
  require(succeeded(protocol::expandAlgorithms(
              *result.module, protocol::AlgorithmExpansionPhase::RetainMaps,
              result.expansion)),
          "source helper expansion failed");
  return result;
}
Operation *product(ModuleOp module) {
  Operation *result = nullptr;
  module.walk([&](Operation *op) {
    auto *meaning = finite::semantics(op);
    if (!result && op->getParentOfType<kernel::ModuleOp>() && meaning &&
        meaning->identity == MathematicalIdentity::FieldMultiply)
      result = op;
  });
  require(result, "missing retained raw multiplication");
  return result;
}
finite::Computation outerCollection(ModuleOp module) {
  Operation *result = nullptr;
  module.walk([&](local::FiniteCollectOp op) { result = op; });
  require(result, "missing source collection");
  finite::Computation computation;
  require(succeeded(finite::describe(result, computation)),
          "source collection description failed");
  return computation;
}
unsigned matvecs(ModuleOp module) {
  unsigned count = 0;
  module.walk([&](Operation *op) {
    auto name = op->getName().getStringRef();
    count += name == "algebra.exec.matrix_mul_vector" ||
             name == "algebra.exec.matrix_transpose_mul_vector";
  });
  return count;
}
// Return a scalar through a nonzero result coordinate and retain another exact
// coordinate. No numerical normalization or additional scalar work is involved.
func::CallOp outlineProduct(Operation *operation) {
  auto unit = operation->getParentOfType<kernel::ModuleOp>();
  OpBuilder builder(unit.getContext());
  builder.setInsertionPointToEnd(&unit.getBody().front());
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
void inlineEntries(ModuleOp module) {
  unsigned remaining = 10000;
  module.walk([&](kernel::ModuleOp unit) {
    auto entry = kernel::getEntry(unit);
    require(bool(entry), "missing raw Kernel entry");
    for (auto iterator = entry.front().begin();
         iterator != entry.front().end();) {
      auto call = dyn_cast<func::CallOp>(&*iterator++);
      if (!call)
        continue;
      require(remaining--, "test entry substitution exceeded its bound");
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
void pinCallbackResult(ModuleOp module) {
  auto outer = outerCollection(module);
  auto view = finite::analyzeComputation(outer);
  require(view && view->nested.size() == 1, "missing nested callback");
  auto helper = cast<local::FuncOp>(view->nested.front().computation.helper);
  auto &end = helper.getBody().front().back();
  Type field = end.getOperand(0).getType();
  auto domain = cast<algebra::FieldType>(field).getDomain();
  protocol::BindingApplication application{"field.add", {domain.str()}, ""};
  auto implementation = protocol::defaultImplementation(application);
  require(bool(implementation), "missing pinned field implementation");
  OpBuilder builder(helper);
  auto binding = local::OperationBindingOp::create(
      builder, helper.getLoc(), "pinned_sum", "field.add",
      builder.getArrayAttr({builder.getStringAttr(domain)}), *implementation);
  builder.setInsertionPoint(&end);
  // Pin an exact existing scalar operation without introducing raw math into
  // Local.
  auto zero = end.getOperand(0);
  OperationState state(helper.getLoc(),
                       protocol::boundOperationName("field.add"));
  state.addOperands({end.getOperand(0), zero});
  state.addTypes(field);
  state.addAttribute("binding",
                     FlatSymbolRefAttr::get(binding.getSymNameAttr()));
  state.addAttribute("parameters", builder.getArrayAttr({}));
  state.addAttribute("site", builder.getStringAttr("pinned_sum"));
  end.setOperand(0, builder.create(state)->getResult(0));
}
void routeOuterInputs(ModuleOp module) {
  auto computation = outerCollection(module);
  auto helper = cast<local::FuncOp>(computation.helper);
  local::ApplyOp inner;
  helper.walk([&](local::ApplyOp call) { inner = call; });
  require(bool(inner), "missing nested call for input routing");
  OpBuilder builder(helper);
  OperationState unitState(helper.getLoc(),
                           kernel::ModuleOp::getOperationName());
  unitState.addAttribute("sym_name", builder.getStringAttr("routing"));
  unitState.addRegion();
  auto unit = cast<kernel::ModuleOp>(builder.create(unitState));
  unit.getBody().emplaceBlock();
  builder.setInsertionPointToEnd(&unit.getBody().front());
  SmallVector<Type> types(inner->getOperandTypes());
  auto entry = func::FuncOp::create(builder, helper.getLoc(), "entry",
                                    builder.getFunctionType(types, types));
  builder.setInsertionPointToEnd(entry.addEntryBlock());
  func::ReturnOp::create(builder, helper.getLoc(), entry.getArguments());
  builder.setInsertionPoint(inner);
  OperationState callState(helper.getLoc(), kernel::CallOp::getOperationName());
  callState.addOperands(inner->getOperands());
  callState.addTypes(types);
  callState.addAttribute(
      "callee", SymbolRefAttr::get(
                    module.getContext(), "routing",
                    {FlatSymbolRefAttr::get(module.getContext(), "entry")}));
  callState.addAttribute("site", builder.getStringAttr("routing"));
  auto *routing = builder.create(callState);
  inner->setOperands(routing->getResults());
}
void refusesSource(ModuleOp source, ModuleOp candidate,
                   const protocol::AlgorithmExpansionState &before,
                   const protocol::AlgorithmExpansionState &after) {
  // Give the stale numerical candidate the identical mutated helper context.
  // Refusal must come from rereading the actual source collection, rather than
  // merely noticing a different surrounding helper or Kernel declaration.
  auto *sourceUnit = &source.getBody()->front();
  auto *candidateUnit = &candidate.getBody()->front();
  for (auto &operation : sourceUnit->getRegion(0).front()) {
    if (isa<local::FiniteCollectOp>(operation))
      continue;
    auto *replacement = SymbolTable::lookupSymbolIn(
        candidateUnit, SymbolTable::getSymbolName(&operation));
    OpBuilder builder(candidate.getContext());
    if (replacement)
      builder.setInsertionPoint(replacement);
    else {
      Operation *next = operation.getNextNode();
      Operation *anchor = nullptr;
      for (; next && !anchor; next = next->getNextNode())
        anchor = SymbolTable::lookupSymbolIn(candidateUnit,
                                             SymbolTable::getSymbolName(next));
      if (anchor)
        builder.setInsertionPoint(anchor);
      else
        builder.setInsertionPointToEnd(&candidateUnit->getRegion(0).front());
    }
    builder.clone(operation);
    if (replacement)
      replacement->erase();
  }
  bool named = false;
  ScopedDiagnosticHandler quiet(
      source.getContext(), [&](Diagnostic &diagnostic) {
        for (const auto &refusal : diagnostics::refusals(diagnostic))
          named |= refusal.code == "nested-contraction-correspondence";
        return success();
      });
  require(succeeded(verify(source)), "source mutation was not admitted");
  require(succeeded(verify(candidate)),
          "stale numerical candidate was not admitted");
  require(
      failed(nested::verifyFiniteCollections(source, candidate, before, after)),
      "independent reader accepted changed actual source");
  require(named, "missing nested source correspondence diagnostic");
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
              std::string text = replace(fixture(mathematics), ",seed,fn",
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
              auto prepared =
                  parseSourceString<ModuleOp>(original.bytes(), &context);
              require(bool(prepared), "original source IR refused");
              require(
                  succeeded(mathematical::expandMathRealizations(*prepared)),
                  "math helper realization failed");
              unsigned retained = 0, rawCalls = 0;
              prepared->walk([&](kernel::CallOp) { ++retained; });
              prepared->walk([&](func::CallOp op) {
                rawCalls += bool(op->getParentOfType<kernel::ModuleOp>());
              });
              require(!mathematics || (retained && rawCalls),
                      "source test no longer exercises retained helper "
                      "mathematics");
              protocol::AlgorithmExpansionState expansion;
              require(
                  succeeded(protocol::expandAlgorithms(
                      *prepared, protocol::AlgorithmExpansionPhase::RetainMaps,
                      expansion)),
                  "transparent helper expansion failed");
              OwningOpRef<ModuleOp> before(
                  cast<ModuleOp>((*prepared)->clone()));
              auto beforeExpansion = expansion;
              require(succeeded(nested::rewriteFiniteCollections(*prepared,
                                                                 expansion)),
                      "nested source rewrite failed");
              require(succeeded(nested::verifyFiniteCollections(
                          *before, *prepared, beforeExpansion, expansion)),
                      "nested source comparison failed");
              unsigned matvecs = 0, loops = 0;
              prepared->walk([&](Operation *op) {
                auto name = op->getName().getStringRef();
                matvecs += name == "algebra.exec.matrix_mul_vector" ||
                           name == "algebra.exec.matrix_transpose_mul_vector";
                loops += isa<local::LocalForOp>(op);
              });
              require(matvecs == 1 && !loops,
                      "source spelling missed whole collection strategy");
              // Exercise the parent preparation slot and the compiler's
              // independent composed correspondence, including the retained
              // original closure.
              take(language::compileEntry(original));
              take(language::compileEntry(original, {false, false}));
            });
  for (bool routing : {false, true})
    cases.run(
        routing ? "Kernel result input routing"
                : "direct Kernel entry mathematics",
        [&] {
          auto input = prepare(context);
          if (routing)
            routeOuterInputs(*input.module);
          else
            inlineEntries(*input.module);
          require(succeeded(verify(*input.module)), "direct raw entry refused");
          OwningOpRef<ModuleOp> source(cast<ModuleOp>(input.module->clone()));
          auto before = input.expansion;
          require(succeeded(nested::rewriteFiniteCollections(
                      *input.module, input.expansion)) &&
                      matvecs(*input.module) == 1,
                  "direct raw entry missed source matrix strategy");
          require(succeeded(nested::verifyFiniteCollections(
                      *source, *input.module, before, input.expansion)),
                  "independent direct-entry reading failed");
        });
  cases.run("exact helper substitution and source return coordinates", [&] {
    auto input = prepare(context);
    auto call = outlineProduct(product(*input.module));
    require(succeeded(verify(*input.module)), "outlined raw source refused");
    auto computation = outerCollection(*input.module);
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
              "callback return coordinate lost its exact SSA substitution");
    require(view->sourceOperation(inner.occurrence) != inner.occurrence ||
                !view->numericalBody,
            "temporary nested call has no original source instruction");
    auto helper = SymbolTable::lookupNearestSymbolFrom<func::FuncOp>(
        call, call.getCalleeAttr());
    require(bool(helper), "outlined helper lookup failed");
    OwningOpRef<ModuleOp> source(cast<ModuleOp>(input.module->clone()));
    auto before = input.expansion;
    require(succeeded(nested::rewriteFiniteCollections(*input.module,
                                                       input.expansion)),
            "outlined numerical closure rewrite failed");
    require(matvecs(*input.module) == 1,
            "exact multi-result helper missed source matrix strategy");
    require(succeeded(nested::verifyFiniteCollections(*source, *input.module,
                                                      before, input.expansion)),
            "independent reader lost exact result coordinate");
    auto *rawProduct = product(*source);
    auto rawHelper = rawProduct->getParentOfType<func::FuncOp>();
    auto &returned = rawHelper.front().back();
    require(returned.getNumOperands() == 2, "missing multi-result return");
    Value first = returned.getOperand(0);
    returned.setOperand(0, returned.getOperand(1));
    returned.setOperand(1, first);
    refusesSource(*source, *input.module, before, input.expansion);
  });
  for (StringRef change :
       {"dead arithmetic", "dead helper invocation", "actual operand",
        "Kernel operand", "policy", "implementation pin"})
    cases.run("retained source refusal: " + change, [&] {
      auto input = prepare(context);
      OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(input.module->clone()));
      auto accepted = input.expansion;
      require(
          succeeded(nested::rewriteFiniteCollections(*candidate, accepted)) &&
              matvecs(*candidate) == 1,
          "missing positive candidate for independent refusal");
      if (change == "dead arithmetic") {
        auto *operation = product(*input.module);
        OpBuilder builder(operation);
        builder.clone(*operation);
      } else if (change == "dead helper invocation") {
        auto call = outlineProduct(product(*input.module));
        OpBuilder builder(call);
        builder.clone(*call);
      } else if (change == "actual operand") {
        auto *operation = product(*input.module);
        operation->setOperand(1, operation->getOperand(0));
      } else if (change == "Kernel operand") {
        auto view = finite::analyzeComputation(outerCollection(*input.module));
        require(view && view->nested.size() == 1, "missing nested source step");
        auto helper =
            cast<local::FuncOp>(view->nested.front().computation.helper);
        bool changed = false;
        helper.walk([&](kernel::CallOp call) {
          for (auto [index, operand] : llvm::enumerate(call.getOperands()))
            if (!changed && operand == helper.getArgument(1)) {
              call->setOperand(index, helper.getArgument(0));
              changed = true;
            }
        });
        require(changed, "missing actual item at Kernel call boundary");
      } else if (change == "implementation pin") {
        pinCallbackResult(*input.module);
      } else {
        input.module->walk([&](kernel::CallOp call) {
          Builder builder(&context);
          call->setAttr("policy",
                        builder.getBoolArrayAttr({false, true, false}));
        });
      }
      refusesSource(*input.module, *candidate, input.expansion, accepted);
      OwningOpRef<ModuleOp> unchanged(cast<ModuleOp>(input.module->clone()));
      require(succeeded(nested::rewriteFiniteCollections(*input.module,
                                                         input.expansion)),
              "retained unsupported payload did not keep fallback");
      require(OperationEquivalence::isEquivalentTo(
                  unchanged->getOperation(), input.module->getOperation(),
                  OperationEquivalence::IgnoreLocations),
              "unsupported retained payload was replaced");
    });
  cases.run("effectful callback keeps ordered fallback", [&] {
    auto text = replace(fixture(), "=>s+multiply(a,b)",
                        "=>{require true;s+multiply(a,b)}");
    auto captured =
        take(language::capture({{"sample", text, "nested-effect.zkc"}}));
    auto checked = take(language::analyze(captured).checkedProject());
    auto entry = take(closeProtocolDeployment(checked, "sample::Demo"));
    auto original = take(language::prepareOriginal(entry));
    auto prepared = parseSourceString<ModuleOp>(original.bytes(), &context);
    require(bool(prepared), "effectful source refused");
    require(succeeded(mathematical::expandMathRealizations(*prepared)),
            "math realization failed");
    protocol::AlgorithmExpansionState expansion;
    require(succeeded(protocol::expandAlgorithms(
                *prepared, protocol::AlgorithmExpansionPhase::RetainMaps,
                expansion)),
            "helper expansion failed");
    OwningOpRef<ModuleOp> before(cast<ModuleOp>((*prepared)->clone()));
    require(succeeded(nested::rewriteFiniteCollections(*prepared, expansion)),
            "effectful fallback failed");
    require(OperationEquivalence::isEquivalentTo(
                before->getOperation(), prepared->getOperation(),
                OperationEquivalence::IgnoreLocations),
            "effectful source was replaced");
    take(language::compileEntry(original));
  });
  return cases.result();
}
