#include "../lib/Transforms/Computation/Support.h"
#include "../lib/Transforms/MathematicalSupport.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/ComputationRecipes.h"
#include "support/NativeCases.h"
#include "support/ScopedComputation.h"
#include "support/ScopedFinite.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Target/Cpu/Passes.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/Support/MemoryBuffer.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
std::string replace(StringRef source, StringRef from, StringRef to) {
  auto text = source.str();
  auto pos = text.find(from.str());
  require(pos != std::string::npos, "missing fixture edit " + from);
  text.replace(pos, from.size(), to.str());
  return text;
}
OwningOpRef<ModuleOp> copy(ModuleOp module) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(module->clone()));
}
protocol_ir::ProtocolModuleOp owner(ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
func::FuncOp function(ModuleOp module, StringRef name = "work") {
  auto result = SymbolTable(owner(module)).lookup<func::FuncOp>(name);
  require(bool(result), "missing function " + name);
  return result;
}
void logical(ModuleOp module) {
  PassManager manager(module.getContext());
  manager.addPass(protocol::createProjectProtocolPass(false));
  manager.addPass(protocol::createLowerMathPass());
  require(succeeded(manager.run(module)), "scoped demand lowering failed");
}
void materialize(ModuleOp module) {
  logical(module);
  require(succeeded(computation::realizeComputations(module)),
          "numerical realization failed");
}
OwningOpRef<ModuleOp> close(func::FuncOp helper) {
  uint64_t remaining = 1000000;
  auto result = computation::closeComputation(helper, remaining);
  require(bool(result), "mathematical closure refused");
  return result;
}
} // namespace
int main(int argc, char **argv) {
  require(argc == 2, "expected a mathematical fixture path");
  auto bytes = llvm::MemoryBuffer::getFile(argv[1]);
  require(bool(bytes), "cannot read mathematical fixture");
  StringRef fixture = (*bytes)->getBuffer();
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  for (StringRef mutation :
       {"foreign condition", "non-Boolean condition", "empty occurrence"})
    cases.run("formation refuses " + mutation, [&] {
      auto module = parseSourceString<ModuleOp>(R"mlir(module {
        func.func @work(%condition:i1, %index:ui64) -> i1 {
          func.return %condition : i1
        }
        func.func @other(%condition:i1) -> i1 {
          func.return %condition : i1
        }
      })mlir",
                                                &context);
      require(bool(module), "guard formation fixture refused");
      auto before = copy(*module);
      SymbolTable symbols(*module);
      auto wrapper = symbols.lookup<func::FuncOp>("work");
      auto other = symbols.lookup<func::FuncOp>("other");
      computation::CalculationGuard guard{
          mutation == "foreign condition"       ? other.getArgument(0)
          : mutation == "non-Boolean condition" ? wrapper.getArgument(1)
                                                : wrapper.getArgument(0),
          StringAttr::get(&context,
                          mutation == "empty occurrence" ? "" : "check")};
      std::string diagnostic;
      ScopedDiagnosticHandler quiet(&context, [&](Diagnostic &message) {
        llvm::raw_string_ostream out(diagnostic);
        message.print(out);
        return success();
      });
      require(
          failed(computation::formCalculation(wrapper, *module, {}, guard)) &&
              namesIdentifier(diagnostic, "computation-formation"),
          "malformed guard input passed formation");
      require(OperationEquivalence::isEquivalentTo(
                  *module, *before, OperationEquivalence::IgnoreLocations),
              "refused formation changed the wrapper");
    });
  auto source = parseSourceString<ModuleOp>(fixture, &context);
  require(bool(source), "realization fixture refused");
  auto frozen = copy(*source);
  logical(*frozen);
  auto executable = copy(*frozen);
  require(succeeded(computation::realizeComputations(*executable)),
          "fixture lowering failed");
  cases.run("polynomial mathematics stays exact until realization", [&] {
    auto request = cast<exec::ComputeOp>(function(*frozen).front().front());
    SymbolTableCollection symbols;
    auto helper = request.resolveCallee(symbols);
    require(bool(helper), "missing actual computation closure");
    auto numerical = close(helper);
    bool retainedPolynomial = false;
    numerical->walk(
        [&](poly::MultiplyPolynomialOp) { retainedPolynomial = true; });
    require(retainedPolynomial, "preparation erased the raw polynomial DAG");
    require(succeeded(computation::verifyComputationClosure(
                helper->getParentOp(), helper, *numerical)),
            "closure changed original mathematics");
    bool polynomial = false;
    executable->walk([&](Operation *op) {
      for (auto type : op->getResultTypes())
        polynomial |= isa<poly::PolynomialType>(type);
    });
    auto calls = scopedFinite::applications(function(*executable));
    require(!polynomial && !calls.empty(),
            "formal data escaped or evaluation vanished");
    for (auto call : calls)
      for (auto value : scopedComputation::payload(call))
        require(!value.use_empty(),
                "unused total recipe became executable work");
    require(succeeded(computation::verifyComputationRealization(*frozen,
                                                                *executable)),
            "actual computation recipe comparison failed");
  });
  for (bool simplify : {false, true})
    cases.run(simplify ? "full optimized pipeline"
                       : "full unsimplified pipeline",
              [&] {
                auto module = copy(*source);
                PassManager manager(&context);
                manager.addPass(protocol::createProjectProtocolPass(simplify));
                manager.addPass(protocol::createLowerMathPass());
                manager.addPass(protocol::createSelectPhysicalPass());
                require(succeeded(manager.run(*module)),
                        "realized program did not compile");
                module->walk([&](Operation *op) {
                  require(!isa<exec::ComputeOp>(op),
                          "preparation construct escaped into execution");
                  if (auto f = dyn_cast<func::FuncOp>(op))
                    require(protocol::isScopedExecutionFunction(f),
                            "mathematical function survived selection");
                });
              });
  auto refusal = [&](StringRef label, StringRef text, StringRef code,
                     bool semantic = false) {
    cases.run(label, [&] {
      std::string messages;
      ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
        messages += diagnostic.str();
        return success();
      });
      auto module = parseSourceString<ModuleOp>(text, &context);
      if (semantic) {
        require(bool(module), "semantic mutation must remain formed");
        require(failed(zkc::admitStage(*module)),
                "invalid computation admitted");
      } else
        require(!module, "invalid computation formed");
      require(namesIdentifier(messages, code),
              "unexpected refusal: " + messages);
    });
  };
  refusal("missing helper",
          replace(fixture, "callee = @polynomial", "callee = @missing"),
          "execution-computation-symbol");
  refusal("ordered helper",
          replace(fixture, "callee = @polynomial", "callee = @work"),
          "execution-computation-symbol");
  refusal("wrong signature",
          replace(replace(fixture, "%arg0, %arg1, %arg2, %arg3",
                          "%arg0, %arg1, %arg2"),
                  "(!runtime.scope, !F, !F, !F) -> !exec.outcome",
                  "(!runtime.scope, !F, !F) -> !exec.outcome"),
          "execution-computation-signature");
  refusal("extra computation attribute",
          replace(fixture, "site = \"evaluate\"",
                  "site = \"evaluate\", extra = true"),
          "mlir-unknown-property");
  refusal("unused under-width observation",
          replace(fixture, "   %r = \"poly.evaluate\"",
                  "   %unused = \"poly.coefficients\"(%q) : (!P)->!A\n   %r "
                  "= \"poly.evaluate\""),
          "polynomial-formation", true);
  cases.run("non-protocol numerical context", [&] {
    auto module = parseSourceString<ModuleOp>(
        "module { func.func private @empty() {func.return} }", &context);
    require(bool(module), "standalone function refused");
    auto before = copy(*module);
    ScopedDiagnosticHandler handler(&context,
                                    [](Diagnostic &) { return success(); });
    require(failed(computation::realizeComputations(*module)) &&
                OperationEquivalence::isEquivalentTo(
                    *module, *before, OperationEquivalence::IgnoreLocations),
            "non-protocol realization was accepted or modified");
  });
  refusal("formal value at computation signature",
          replace(fixture, "    func.func @work", R"(
 func.func private @formal(%p:!P)->!P {func.return %p:!P}
 func.func @formal_exec(%scope:!runtime.scope,%p:!P)->!exec.outcome<(!P)> attributes {no_inline,runtime.origin=["formal_exec",[]]} {
   %call = "exec.compute"(%scope,%p) {callee=@formal,site="formal"}:(!runtime.scope,!P)->!exec.outcome<(!P)>
   "exec.dispatch"(%call)[^done,^failed]:(!exec.outcome<(!P)>)->()
 ^done(%value:!P):
   %result = "exec.returned"(%value):(!P)->!exec.outcome<(!P)>
   func.return %result:!exec.outcome<(!P)>
 ^failed(%stop:!exec.stop):
   %failure = "exec.failed"(%stop):(!exec.stop)->!exec.outcome<(!P)>
   func.return %failure:!exec.outcome<(!P)>
 }
    func.func @work)"),
          "execution-source-closure", true);
  refusal("protocol call cannot bypass scoped computation",
          replace(fixture, "callee=@work", "callee=@polynomial"),
          "interactive-call-type");
  auto withHelper = [&](StringRef definitions, StringRef name,
                        StringRef caller) {
    auto text = replace(fixture, "    func.func @work",
                        definitions.str() + "\n    func.func @work");
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "extra helper fixture refused");
    scopedComputation::computation(function(*module, name), caller);
    require(succeeded(zkc::admitStage(*module)),
            "extra scoped computation refused");
    return module;
  };
  cases.run("multiple computations and nested helpers", [&] {
    auto module = withHelper(R"(
 func.func private @nested(%a:!F,%b:!F,%x:!F)->!F {
   %r=func.call @polynomial(%a,%b,%x):(!F,!F,!F)->!F
   func.return %r:!F
 })",
                             "nested", "second");
    materialize(*module);
    require(!scopedFinite::applications(function(*module, "second")).empty(),
            "nested computation disappeared");
  });
  cases.run("independent helper recipe comparison", [&] {
    auto numerical =
        computationRecipeSource(owner(*source), "polynomial", "realized");
    auto entry = mathematical::getComputationEntry(*numerical);
    auto &block = entry.front();
    while (!block.empty())
      block.back().erase();
    OpBuilder builder(&block, block.end());
    auto product = algebra::FieldMultiplyOp::create(
        builder, entry.getLoc(), block.getArgument(0).getType(),
        block.getArgument(0), block.getArgument(1));
    func::ReturnOp::create(builder, entry.getLoc(), product.getResult());
    mathematical::RealizationWork work;
    auto candidate = realizeComputationEntry(*numerical, "product", {}, work);
    require(bool(candidate), "direct recipe lowering failed");
    computationRecipeOutput(*candidate);
    require(succeeded(computation::verifyEntryRecipes(*numerical, *candidate,
                                                      "product")),
            "valid recipe comparison failed");
    ScopedDiagnosticHandler handler(&context,
                                    [](Diagnostic &) { return success(); });
    require(failed(computation::verifyEntryRecipes(*numerical, *candidate,
                                                   "different_call")),
            "different call site escaped comparison");
    auto wrongSite = copy(*candidate);
    scopedFinite::application(function(*wrongSite, "realized"), "field.mul")
        .setSite("different_product");
    require(failed(computation::verifyEntryRecipes(*numerical, *wrongSite,
                                                   "product")),
            "changed site escaped comparison");
    auto call = scopedFinite::application(function(*candidate, "realized"),
                                          "field.mul");
    call->setOperand(2, call.getInputs()[0]);
    require(succeeded(verify(*candidate)), "operand mutation lost formation");
    require(failed(computation::verifyEntryRecipes(*numerical, *candidate,
                                                   "product")),
            "changed operand escaped independent recipe verification");
  });
  cases.run(
      "prefix restriction has an independently checked ordered recipe", [&] {
        auto numerical = parseSourceString<ModuleOp>(R"(
!V = !data.field_vector<"bls12-381.fr">
module @restriction attributes {exec.computation} {
  func.func @realized(%values:!V,%point:!V)->!V {
    %r = "algebra.multilinear_restrict_prefix"(%values,%point):(!V,!V)->!V
    func.return %r:!V
  }
})",
                                                     &context);
        require(bool(numerical), "prefix restriction recipe source refused");
        mathematical::RealizationWork work;
        auto candidate =
            realizeComputationEntry(*numerical, "restrict", {}, work);
        require(bool(candidate), "prefix restriction recipe failed");
        computationRecipeOutput(*candidate);
        require(succeeded(computation::verifyEntryRecipes(
                    *numerical, *candidate, "restrict")),
                "prefix restriction recipe did not pass independent checking");
        auto wrong = copy(*candidate);
        auto operation = scopedFinite::application(
            function(*wrong, "realized"), "multilinear.restrict_prefix");
        require(operation && operation.getInputs().size() == 2,
                "prefix restriction did not preserve both vector ports");
        Value first = operation.getInputs()[0],
              second = operation.getInputs()[1];
        operation->setOperand(1, second);
        operation->setOperand(2, first);
        require(succeeded(verify(*wrong)),
                "ordered operand mutation lost scoped formation");
        ScopedDiagnosticHandler handler(&context,
                                        [](Diagnostic &) { return success(); });
        require(failed(computation::verifyEntryRecipes(*numerical, *wrong,
                                                       "restrict")),
                "reordered prefix restriction operands escaped checking");
      });
  cases.run("static dimension discards unused field-array construction", [&] {
    auto module = withHelper(R"(
 func.func private @dimension(%a:!F,%b:!F)->ui64 {
   %v = "data.array_from_elements"(%a,%b):(!F,!F)->!A
   %n = "data.dim"(%v){axis=0:i64}:(!A)->ui64
   func.return %n:ui64
 })",
                             "dimension", "dimension_exec");
    materialize(*module);
    auto calls =
        scopedFinite::applications(function(*module, "dimension_exec"));
    require(calls.size() == 1 &&
                scopedFinite::contract(calls[0]) == "index.constant",
            "static dimension emitted field-array construction");
  });
  cases.run("dynamic byte dimension uses the byte length recipe", [&] {
    auto module = withHelper(R"(
 func.func private @byte_dimension(%bytes:!data.bytes)->ui64 {
   %n = "data.dim"(%bytes){axis=0:i64}:(!data.bytes)->ui64
   func.return %n:ui64
 })",
                             "byte_dimension", "byte_dimension_exec");
    materialize(*module);
    auto calls =
        scopedFinite::applications(function(*module, "byte_dimension_exec"));
    require(calls.size() == 1 &&
                scopedFinite::contract(calls[0]) == "bytes.length",
            "byte dimension selected a different container recipe");
  });
  cases.run("array recipe rejects shortened vector construction", [&] {
    auto numerical =
        computationRecipeSource(owner(*source), "polynomial", "realized");
    auto entry = mathematical::getComputationEntry(*numerical);
    auto &block = entry.front();
    while (!block.empty())
      block.back().erase();
    OpBuilder builder(&block, block.end());
    auto array = data::ArrayFromElementsOp::create(
        builder, entry.getLoc(),
        data::FieldArrayType::get(
            &context,
            cast<algebra::FieldType>(block.getArgument(0).getType())
                .getDomain(),
            2),
        ValueRange{block.getArgument(0), block.getArgument(1)});
    auto at = data::ArrayAtOp::create(
        builder, entry.getLoc(), block.getArgument(0).getType(),
        array.getResult(), builder.getI64IntegerAttr(1));
    func::ReturnOp::create(builder, entry.getLoc(), at.getResult());
    // Keep the construction intact so these mutations exercise the reader.
    mathematical::RealizationWork work;
    auto candidate = realizeComputationEntry(*numerical, "array", {}, work);
    require(bool(candidate), "array recipe failed");
    require(succeeded(computation::verifyEntryRecipes(*numerical, *candidate,
                                                      "array")),
            "valid array recipe comparison failed");
    for (bool changeBinding : {false, true}) {
      auto mutated = copy(*candidate);
      auto access = scopedFinite::application(function(*mutated, "realized"),
                                              "field_array.at");
      if (changeBinding) {
        auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
            access, access.getBindingAttr());
        binding->setAttr(
            "arguments",
            builder.getArrayAttr({builder.getStringAttr("bls12-381.fr"),
                                  builder.getIntegerAttr(
                                      builder.getIntegerType(64, false), 3)}));
      } else
        access.setParametersAttr(builder.getArrayAttr(
            {builder.getIntegerAttr(builder.getIntegerType(64, false), 0)}));
      ScopedDiagnosticHandler handler(&context,
                                      [](Diagnostic &) { return success(); });
      require(failed(computation::verifyEntryRecipes(*numerical, *mutated,
                                                     "array")),
              "changed array contract instance accepted");
    }
    auto append = scopedFinite::applications(function(*candidate, "realized"),
                                             "vector.append");
    require(!append.empty(), "array recipe did not append");
    auto last = append.back();
    scopedComputation::omit(last, last.getInputs()[0]);
    require(succeeded(computation::verifyRecipeOutput(*candidate)),
            "short array mutation not formed");
    ScopedDiagnosticHandler handler(&context,
                                    [](Diagnostic &) { return success(); });
    require(failed(computation::verifyEntryRecipes(*numerical, *candidate,
                                                   "array")),
            "short vector accepted by recipe comparison");
  });
  auto large = [&](unsigned repetitions) {
    std::string text = "func.func private @leaf(%x:!F)->!F {\n";
    for (unsigned i = 0; i < 250; ++i)
      text += "%v" + std::to_string(i) +
              " = algebra.field_add %x,%x : (!F,!F)->!F\n";
    text += "func.return %x:!F }\n func.func private @expanded(%x:!F)->!F {\n";
    for (unsigned i = 0; i < repetitions; ++i)
      text += "%v" + std::to_string(i) + " = func.call @leaf(%x):(!F)->!F\n";
    text += "func.return %x:!F }\n";
    return replace(fixture, "    func.func @work",
                   text + "    func.func @work");
  };
  // Selected units and source helpers have the same occurrence allowance.
  // These roots are intentionally dormant: liveness grants no admission bypass.
  for (bool selected : {false, true}) {
    auto request = [&](ModuleOp module, StringRef name) {
      auto caller =
          scopedComputation::computation(function(module, "expanded"), name);
      if (selected) {
        auto target = SymbolTable(owner(module)).lookup<ModuleOp>("selected");
        if (!target) {
          auto closed = close(function(module, "expanded"));
          closed->setSymName("selected");
          target = closed.release();
          owner(module).getBody().front().push_back(target);
        }
        auto entry = mathematical::getComputationEntry(target);
        cast<exec::ComputeOp>(caller.front().front())
            .setCalleeAttr(SymbolRefAttr::get(
                target.getSymNameAttr(),
                {FlatSymbolRefAttr::get(entry.getSymNameAttr())}));
      }
    };
    cases.run(selected ? "selected computation shared expansion budget"
                       : "source helper shared expansion budget",
              [&] {
                auto module = parseSourceString<ModuleOp>(large(220), &context);
                require(bool(module), "single helper budget control refused");
                request(*module, "large1");
                require(succeeded(zkc::admitStage(*module)),
                        "one large occurrence must be admitted");
                request(*module, "large2");
                std::string diagnostic;
                ScopedDiagnosticHandler handler(&context, [&](Diagnostic &d) {
                  diagnostic += d.str();
                  return success();
                });
                auto checked = zkc::admitStage(*module);
                require(failed(checked) &&
                            namesIdentifier(diagnostic,
                                            "mathematical-analysis-limit"),
                        "shared helper budget was not enforced: " + diagnostic);
              });
    cases.run(
        selected ? "bounded selected computation expansion"
                 : "conservative helper budget admits expandable bodies",
        [&] {
          auto module = parseSourceString<ModuleOp>(large(195), &context);
          require(bool(module), "bounded helper fixture refused");
          request(*module, "large1");
          request(*module, "large2");
          materialize(*module);
          require(
              scopedFinite::applications(function(*module, "large1")).empty() &&
                  scopedFinite::applications(function(*module, "large2"))
                      .empty(),
              "dead total mathematics became reached work");
        });
  }
  auto closureMutation = [&](StringRef name,
                             llvm::function_ref<void(ModuleOp)> change) {
    cases.run(name, [&] {
      auto helper = function(*source, "polynomial");
      auto candidate = close(helper);
      change(*candidate);
      require(succeeded(verify(*candidate)), "closure mutation not formed");
      std::string diagnostic;
      ScopedDiagnosticHandler handler(&context, [&](Diagnostic &d) {
        diagnostic += d.str();
        return success();
      });
      auto result = computation::verifyComputationClosure(owner(*source),
                                                          helper, *candidate);
      require(
          failed(result) &&
              namesIdentifier(diagnostic, "computation-closure-correspondence"),
          "changed original mathematics escaped closure comparison: " +
              diagnostic);
    });
  };
  closureMutation("retained helper result changed", [&](ModuleOp module) {
    auto entry = mathematical::getComputationEntry(module);
    entry.front().back().setOperand(0, entry.getArgument(0));
  });
  closureMutation(
      "polynomial evaluation operand changed", [&](ModuleOp module) {
        bool changed = false;
        module.walk([&](poly::EvaluatePolynomialOp op) {
          op->setOperand(1, op->getParentOfType<func::FuncOp>().getArgument(0));
          changed = true;
        });
        require(changed, "missing polynomial evaluation");
      });
  auto mutation = [&](StringRef label,
                      llvm::function_ref<void(ModuleOp)> change) {
    cases.run(label, [&] {
      auto candidate = copy(*executable);
      change(*candidate);
      require(succeeded(verify(*candidate)), "mutation is not formed");
      std::string diagnostic;
      ScopedDiagnosticHandler handler(&context, [&](Diagnostic &d) {
        diagnostic += d.str();
        return success();
      });
      auto result =
          computation::verifyComputationRealization(*frozen, *candidate);
      require(
          failed(result) &&
              namesIdentifier(diagnostic, "numerical-lowering-correspondence"),
          "numerical comparison accepted mutation: " + diagnostic);
    });
  };
  mutation("realized result replaced by a same-type input",
           [&](ModuleOp module) {
             auto f = function(module);
             scopedComputation::returned(f)->setOperand(0, f.getArgument(1));
           });
  mutation("partial runtime operation inserted", [&](ModuleOp module) {
    auto f = function(module);
    OpBuilder builder(f);
    runtime::BindingOp::create(builder, f.getLoc(), "partial_inverse",
                               "field.inverse",
                               builder.getStrArrayAttr({"bls12-381.fr"}), "");
    auto end = scopedComputation::returned(f);
    auto inverse = scopedComputation::appendApply(
        f, "partial_inverse", end.getValues(), end.getValues().getTypes(),
        "injected_inverse");
    end->setOperands(scopedComputation::payload(inverse));
  });
  mutation("explicit stop inserted", [&](ModuleOp module) {
    auto f = function(module);
    auto end = scopedComputation::returned(f);
    auto first = scopedFinite::applications(f).front();
    auto *failure = cast<exec::DispatchOp>(first->getNextNode()).getStopped();
    auto *returned = end->getNextNode();
    returned->erase();
    OpBuilder builder(end);
    OperationState state(end.getLoc(), exec::RejectOp::getOperationName());
    state.addOperands(f.getArgument(0));
    state.addTypes(exec::StopType::get(&context));
    state.addAttribute("reason", builder.getStringAttr("reject"));
    state.addAttribute("site", builder.getStringAttr("injected"));
    auto rejected = builder.create(state);
    cf::BranchOp::create(builder, end.getLoc(), failure,
                         rejected->getResults());
    end.erase();
  });
  mutation("origin changed", [&](ModuleOp module) {
    function(module)->setAttr(
        "runtime.origin",
        ArrayAttr::get(&context, {StringAttr::get(&context, "unrelated"),
                                  ArrayAttr::get(&context, {})}));
  });
  mutation("unused binding inserted", [&](ModuleOp module) {
    auto f = function(module);
    OpBuilder builder(f);
    runtime::BindingOp::create(builder, f.getLoc(), "extra", "field.add",
                               builder.getStrArrayAttr({"bls12-381.fr"}), "");
  });
  return cases.result();
}
