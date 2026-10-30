#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Transforms/Protocol.h"
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
OwningOpRef<ModuleOp> copy(ModuleOp module) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(module->clone()));
}
func::FuncOp function(ModuleOp module, StringRef name) {
  func::FuncOp result;
  module.walk([&](func::FuncOp op) {
    if (op.getSymName() == name)
      result = op;
  });
  require(bool(result), "missing scoped function");
  return result;
}
Operation *primitive(func::FuncOp function, StringRef contract,
                     unsigned index = 0) {
  Operation *result = nullptr;
  std::function<void(func::FuncOp)> visit = [&](func::FuncOp current) {
    current.walk([&](Operation *op) {
      if (auto call = dyn_cast<func::CallOp>(op)) {
        auto callee = SymbolTable::lookupNearestSymbolFrom<func::FuncOp>(
            call, call.getCalleeAttr());
        if (callee && callee->hasAttr("runtime.region"))
          visit(callee);
      }
      auto binding = op->getAttrOfType<FlatSymbolRefAttr>("binding");
      if (!binding)
        return;
      auto declaration =
          SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(op, binding);
      if (declaration && declaration.getContract() == contract && index-- == 0)
        result = op;
    });
  };
  visit(function);
  require(result != nullptr, "missing primitive occurrence");
  return result;
}
void run(ModuleOp module, std::unique_ptr<Pass> pass) {
  PassManager manager(module.getContext());
  manager.addPass(std::move(pass));
  require(succeeded(manager.run(module)), "fixture pass refused");
}
constexpr StringLiteral algorithm = R"mlir(module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "runtime.binding"() <{arguments = [], contract = "bool.and", implementation = "", sym_name = "and",function_type=(!runtime.scope, i1, i1) -> !exec.outcome<(i1)>}> : () -> ()
    "protocol.func"() <{function_type = (i1, i1) -> i1, input_roles = [["P"], ["P"]], origin = ["main", []], output_roles = [["P"]], roles = ["P"], sym_name = "main"}> ({
    ^bb0(%arg0: i1, %arg1: i1):
      %0 = "protocol.local_call"(%arg0, %arg1) <{callee = @both, role = "P", site = "call"}> : (i1, i1) -> i1
      "protocol.return"(%0) : (i1) -> ()
    }) : () -> ()
    func.func @identity(%arg0: !runtime.scope, %arg1: i1) -> !exec.outcome<(i1)> attributes {no_inline, runtime.origin = ["identity", []]} {
      %0 = "exec.returned"(%arg1) : (i1) -> !exec.outcome<(i1)>
      return %0 : !exec.outcome<(i1)>
    }
    func.func @both(%arg0: !runtime.scope, %arg1: i1, %arg2: i1) -> !exec.outcome<(i1)> attributes {no_inline, runtime.origin = ["both", []]} {
      %0 = call @identity(%arg0, %arg1) {runtime.site = "first"} : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      %2 = call @identity(%arg0, %arg2) {runtime.site = "second"} : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%2)[^bb3, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb2(%3: !exec.stop):  // 3 preds: ^bb0, ^bb1, ^bb3
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(i1)>
      return %4 : !exec.outcome<(i1)>
    ^bb3(%5: i1):  // pred: ^bb1
      %6 = "exec.apply"(%arg0, %1, %5) <{binding = @and, parameters = [], site = "combine"}> : (!runtime.scope, i1, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%6)[^bb4, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb4(%7: i1):  // pred: ^bb3
      %8 = "exec.returned"(%7) : (i1) -> !exec.outcome<(i1)>
      return %8 : !exec.outcome<(i1)>
    }
  }) : () -> ()
}

)mlir";
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  Cases cases;
  auto negative =
      [&](StringRef name, ModuleOp before, ModuleOp after,
          llvm::function_ref<void(ModuleOp)> mutate,
          llvm::function_ref<LogicalResult(ModuleOp, ModuleOp)> checker,
          StringRef expectedCode) {
        cases.run(name, [&] {
          auto candidate = copy(after);
          mutate(*candidate);
          require(succeeded(verify(*candidate)),
                  "mutation must remain well formed");
          bool code = false;
          ScopedDiagnosticHandler handler(
              &context, [&](Diagnostic &diagnostic) {
                code |= diagnostic.str().find(expectedCode.str()) !=
                        std::string::npos;
                return success();
              });
          require(failed(checker(before, *candidate)) && code,
                  "preservation mutation escaped or wrong refusal");
        });
      };
  auto verifyHelpers = [](ModuleOp before, ModuleOp after) {
    return protocol::verifyScopedHelperExpansionPreserved(before, after);
  };
  auto source = parseSourceString<ModuleOp>(algorithm, &context);
  require(bool(source), "algorithm fixture refused");
  auto expanded = protocol::expandScopedHelpers(*source);
  require(bool(expanded), "scoped expansion refused");
  cases.run("actual virtual expansion", [&] {
    require(succeeded(protocol::verifyScopedHelperExpansionPreserved(
                *source, *expanded)),
            "valid expansion refused");
  });
  cases.run("bounded local occurrence names", [&] {
    uint64_t bytes = 1024;
    auto shortName = protocol::algorithmSite({{"a", "b"}}, "s", bytes);
    require(bool(shortName) && *shortName == "lc_1_a_1_b_1_s",
            "short occurrence encoding changed");
    protocol::Assignments path{{std::string(80, 'a'), std::string(80, 'b')}};
    auto longName = protocol::algorithmSite(path, "s", bytes);
    require(bool(longName) && StringRef(*longName).starts_with("lc_h_") &&
                longName->size() == 69,
            "long occurrence was not compacted");
    path[0].second.back() = 'c';
    auto other = protocol::algorithmSite(path, "s", bytes);
    require(bool(other) && *other != *longName, "different local paths alias");
    uint64_t exhausted = 0;
    auto refused = protocol::algorithmSite(path, "s", exhausted);
    require(!refused, "origin bytes were not bounded before construction");
    require(llvm::toString(refused.takeError()) == "algorithm-origin-limit",
            "wrong origin budget refusal");
  });
  std::string longText = algorithm.str();
  const std::string originalOrigin = "runtime.origin = [\"both\", []]";
  const std::string longDefinition(100, 'b');
  longText.replace(longText.find(originalOrigin), originalOrigin.size(),
                   "runtime.origin=[\"" + longDefinition + "\",[]]");
  const std::string wrapper = R"(
 func.func @outer(%scope:!runtime.scope,%x:i1,%y:i1)->!exec.outcome<(i1)>
   attributes {no_inline,runtime.origin=["outer",[]]} {
   %r = func.call @both(%scope,%x,%y) {runtime.site=")" +
                              std::string(40, 'c') + R"("}
       : (!runtime.scope,i1,i1)->!exec.outcome<(i1)>
   "exec.dispatch"(%r)[^done,^failed] : (!exec.outcome<(i1)>)->()
 ^done(%value:i1):
   %out = "exec.returned"(%value) : (i1)->!exec.outcome<(i1)>
   func.return %out : !exec.outcome<(i1)>
 ^failed(%cause:!exec.stop):
   %failure = "exec.failed"(%cause) : (!exec.stop)->!exec.outcome<(i1)>
   func.return %failure : !exec.outcome<(i1)>
 }
)";
  longText.insert(longText.find("    func.func @identity"), wrapper);
  // Scoped occurrence paths identify the actual callee symbol. Its source
  // definition identity is retained separately in the origin receipt.
  for (size_t at = 0; (at = longText.find("@both", at)) != std::string::npos;) {
    longText.replace(at, 5, "@" + longDefinition);
    at += longDefinition.size() + 1;
  }
  auto longSource = parseSourceString<ModuleOp>(longText, &context);
  require(bool(longSource), "long local fixture refused");
  OwningOpRef<ModuleOp> longExpanded;
  cases.run("long local paths retain provenance and correspondence", [&] {
    std::vector<protocol::AlgorithmOrigin> origins;
    longExpanded = protocol::expandScopedHelpers(*longSource, &origins);
    require(bool(longExpanded), "long helper path refused");
    require(succeeded(protocol::verifyScopedHelperExpansionPreserved(
                *longSource, *longExpanded)),
            "long helper correspondence refused");
    auto op = primitive(function(*longExpanded, "outer"), "bool.and");
    auto site = op->getAttrOfType<StringAttr>("site").getValue();
    require(site.starts_with("lc_h_"), "expected compact occurrence");
    require(llvm::any_of(origins,
                         [&](const auto &origin) {
                           return origin.function == "outer" &&
                                  origin.site == site &&
                                  origin.path == protocol::Assignments{
                                                     {std::string(40, 'c'),
                                                      longDefinition}};
                         }),
            "full local path was lost");
  });
  negative(
      "forged compact local occurrence", *longSource, *longExpanded,
      [&](ModuleOp module) {
        auto op = primitive(function(module, "outer"), "bool.and");
        op->setAttr("site", StringAttr::get(&context, "lc_h_forged"));
      },
      verifyHelpers, "algorithm-correspondence");
  negative(
      "wrong helper substitution", *source, *expanded,
      [&](ModuleOp module) {
        auto op = primitive(function(module, "both"), "bool.and");
        op->setOperand(2, op->getOperand(1));
      },
      verifyHelpers, "algorithm-correspondence");
  negative(
      "wrong local return", *source, *expanded,
      [&](ModuleOp module) {
        auto fn = function(module, "both");
        fn.walk(
            [&](exec::ReturnOp op) { op->setOperand(0, fn.getArgument(1)); });
      },
      verifyHelpers, "algorithm-correspondence");
  negative(
      "unused original helper changed", *source, *expanded,
      [&](ModuleOp module) {
        function(module, "identity")
            ->setAttr(
                "runtime.origin",
                ArrayAttr::get(&context, {StringAttr::get(&context, "another"),
                                          ArrayAttr::get(&context, {})}));
      },
      verifyHelpers, "algorithm-correspondence");

  auto physical = copy(*expanded);
  run(*physical, protocol::createProjectProtocolPass());
  run(*physical, protocol::createLowerMathPass());
  require(succeeded(protocol::lowerPhysical(*physical)),
          "physical selection refused");
  auto released = copy(*physical);
  require(succeeded(protocol::releaseLocalStorage(*released)),
          "release refused");
  cases.run("storage and idempotence", [&] {
    require(succeeded(protocol::verifyStoragePreserved(*physical, *released)),
            "valid release refused");
    auto twice = copy(*released);
    require(succeeded(protocol::releaseLocalStorage(*twice)) &&
                succeeded(protocol::verifyStoragePreserved(*released, *twice)),
            "repeated release refused");
  });
  negative(
      "local operand altered after storage selection", *physical, *released,
      [&](ModuleOp module) {
        auto op = primitive(function(module, "both"), "bool.and");
        op->setOperand(2, op->getOperand(1));
      },
      protocol::verifyStoragePreserved, "storage-correspondence");

  negative(
      "existing release removed", *released, *released,
      [&](ModuleOp module) {
        runtime::ReleaseBindingsOp selected;
        module.walk([&](runtime::ReleaseBindingsOp op) { selected = op; });
        require(bool(selected), "missing existing release");
        selected.erase();
      },
      protocol::verifyStoragePreserved, "storage-correspondence");
  auto recipe = parseSourceFile<ModuleOp>(
      std::string(ZKC_MATH_FIXTURES) + "/iterated-sumcheck.mlir", &context);
  require(bool(recipe), "recipe fixture refused");
  cases.run("recipe construction capacity refuses before publication", [&] {
    auto oversized = copy(*recipe);
    poly::RealizeOp initial;
    oversized->walk([&](poly::RealizeOp op) {
      if (op.getKind() == "init")
        initial = op;
    });
    require(bool(initial), "missing initial realization");
    for (unsigned i = 0; i < 20; ++i) {
      auto extra = cast<poly::RealizeOp>(initial->clone());
      extra.setSymName("extra_init_" + std::to_string(i));
      initial->getBlock()->push_back(extra);
    }
    require(succeeded(verify(*oversized)), "capacity fixture must form");
    auto before = copy(*oversized);
    bool diagnosed = false;
    ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
      diagnosed |= diagnostic.str().find("mathematical-expansion-limit") !=
                   std::string::npos;
      return success();
    });
    require(failed(mathematical::expandPolynomialRecipes(*oversized)) &&
                diagnosed,
            "construction work must refuse with its capacity diagnostic");
    require(OperationEquivalence::isEquivalentTo(
                *before, *oversized, OperationEquivalence::IgnoreLocations),
            "failed construction changed the source module");
  });
  auto realized = copy(*recipe);
  require(succeeded(mathematical::expandPolynomialRecipes(*realized)),
          "recipe expansion refused");
  cases.run("all used polynomial realizations", [&] {
    require(succeeded(mathematical::verifyPolynomialRecipesPreserved(
                *recipe, *realized)),
            "valid recipes refused");
  });
  auto recipeNegative = [&](StringRef name,
                            llvm::function_ref<void(ModuleOp)> mutate) {
    negative(name, *recipe, *realized, mutate,
             mathematical::verifyPolynomialRecipesPreserved,
             "polynomial-recipe-correspondence");
  };
  recipeNegative("unexpected generated helper", [&](ModuleOp module) {
    auto original = function(module, "init");
    auto extra = cast<func::FuncOp>(original->clone());
    extra.setSymName("unexpected_init");
    original->getBlock()->push_back(extra);
  });
  recipeNegative("generated source identity changed", [&](ModuleOp module) {
    function(module, "init")
        ->setAttr(
            "runtime.origin",
            ArrayAttr::get(&context, {StringAttr::get(&context, "another_init"),
                                      ArrayAttr::get(&context, {})}));
  });
  recipeNegative("shape check made tautological", [&](ModuleOp module) {
    auto op = primitive(function(module, "init"), "index.equal");
    op->setOperand(2, op->getOperand(1));
  });
  recipeNegative("initial factors permuted", [&](ModuleOp module) {
    function(module, "init").walk([](exec::VariantOp op) {
      Value first = op->getOperand(2);
      op->setOperand(2, op->getOperand(3));
      op->setOperand(3, first);
    });
  });
  recipeNegative("fold uses wrong factor", [&](ModuleOp module) {
    auto fn = function(module, "bind");
    primitive(fn, "poly.fold", 1)
        ->setOperand(1, primitive(fn, "poly.fold")->getOperand(1));
  });
  recipeNegative("suffix pairing uses row twice", [&](ModuleOp module) {
    auto op = primitive(function(module, "round"), "index.add");
    op->setOperand(2, op->getOperand(1));
  });
  recipeNegative("coefficient convolution uses wrong factor",
                 [&](ModuleOp module) {
                   auto op = primitive(function(module, "round"), "field.mul");
                   op->setOperand(2, op->getOperand(1));
                 });
  recipeNegative("terminal state loses original prefix", [&](ModuleOp module) {
    auto fn = function(module, "finish");
    auto *empty = primitive(fn, "poly.empty_point");
    auto dispatch = cast<exec::DispatchOp>(empty->getNextNode());
    auto body = empty->getParentOfType<func::FuncOp>();
    body.walk([&](exec::CompleteOp op) {
      op->setOperand(1, dispatch.getReturned()->getArgument(0));
    });
  });
  recipeNegative("evaluation uses other factor", [&](ModuleOp module) {
    auto fn = function(module, "evaluate");
    primitive(fn, "poly.evaluate", 1)
        ->setOperand(1, primitive(fn, "poly.evaluate")->getOperand(1));
  });
  recipeNegative(
      "shape guard moved after factor evaluation", [&](ModuleOp module) {
        auto fn = function(module, "evaluate");
        auto *guard = primitive(fn, "control.require");
        auto dispatch = cast<exec::DispatchOp>(guard->getNextNode());
        auto *continuation = dispatch.getReturned();
        require(continuation->getNumArguments() == 0, "guard must be unit");
        auto *evaluation = primitive(fn, "poly.evaluate");
        auto target = cast<exec::DispatchOp>(evaluation->getNextNode());
        auto *after = target.getReturned();
        auto *before = guard->getBlock();
        IRRewriter rewriter(&context);
        auto *resumed = rewriter.splitBlock(after, after->begin());
        guard->remove();
        dispatch->remove();
        // Remove the edge before deleting its old destination. Detached
        // operations still own their successor uses.
        dispatch->setSuccessor(resumed, 0);
        require(continuation->use_empty(), "guard continuation must be unique");
        rewriter.mergeBlocks(continuation, before);
        after->push_back(guard);
        after->push_back(dispatch);
      });
  return cases.result();
}
