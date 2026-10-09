#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/IR.h"
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
local::FuncOp function(ModuleOp module, StringRef name) {
  local::FuncOp result;
  module.walk([&](local::FuncOp op) {
    if (op.getSymName() == name)
      result = op;
  });
  require(bool(result), "missing local function");
  return result;
}
Operation *primitive(local::FuncOp function, StringRef contract,
                     unsigned index = 0) {
  Operation *result = nullptr;
  function.walk([&](Operation *op) {
    auto binding = op->getAttrOfType<FlatSymbolRefAttr>("binding");
    if (!binding)
      return;
    auto declaration =
        SymbolTable::lookupNearestSymbolFrom<local::OperationBindingOp>(
            op, binding);
    if (declaration && declaration.getContract() == contract && index-- == 0)
      result = op;
  });
  require(result != nullptr, "missing primitive occurrence");
  return result;
}
void run(ModuleOp module, std::unique_ptr<Pass> pass) {
  PassManager manager(module.getContext());
  manager.addPass(std::move(pass));
  require(succeeded(manager.run(module)), "fixture pass refused");
}
constexpr StringLiteral algorithm = R"mlir(module { "protocol.module"() ({
 "local.binding"() {sym_name="and",contract="bool.and",arguments=[],implementation=""} : ()->()
 local.func @identity(%x:i1) -> i1 attributes {logical_origin=["identity",[]]} { return %x : i1 }
 local.func @both(%x:i1,%y:i1) -> i1 attributes {logical_origin=["both",[]]} {
   %a = apply @identity(%x) {site="first"} : (i1)->i1
   %b = apply @identity(%y) {site="second"} : (i1)->i1
   %r = "algebra.exec.bool_and"(%a,%b) {binding=@and,parameters=[],site="combine"} : (i1,i1)->i1
   return %r : i1
 }
 "protocol.func"() ({ ^entry(%x:i1,%y:i1):
   %r = "protocol.local_call"(%x,%y) {callee=@both,role="P",site="call"} : (i1,i1)->i1
   "protocol.return"(%r) : (i1)->()
 }) {sym_name="main",function_type=(i1,i1)->i1,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
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
  auto source = parseSourceString<ModuleOp>(algorithm, &context);
  require(bool(source), "algorithm fixture refused");
  auto expanded = copy(*source);
  require(succeeded(protocol::expandAlgorithms(*expanded)),
          "expansion refused");
  cases.run("actual virtual expansion", [&] {
    require(succeeded(protocol::verifyAlgorithmExpansionPreserved(*source,
                                                                  *expanded)),
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
  const std::string originalOrigin = "logical_origin=[\"both\",[]]";
  const std::string longDefinition(100, 'b');
  longText.replace(longText.find(originalOrigin), originalOrigin.size(),
                   "logical_origin=[\"" + longDefinition + "\",[]]");
  const std::string wrapper = "local.func @outer(%x:i1,%y:i1) -> i1 attributes "
                              "{logical_origin=[\"outer\",[]]} {\n"
                              " %r = apply @both(%x,%y) {site=\"" +
                              std::string(40, 'c') +
                              "\"} : (i1,i1)->i1\n return %r : i1\n }\n";
  longText.insert(longText.find(" \"protocol.func\""), wrapper);
  auto longSource = parseSourceString<ModuleOp>(longText, &context);
  require(bool(longSource), "long local fixture refused");
  auto longExpanded = copy(*longSource);
  cases.run("long local paths retain provenance and correspondence", [&] {
    std::vector<protocol::AlgorithmOrigin> origins;
    require(succeeded(protocol::expandAlgorithms(*longExpanded, &origins)),
            "long helper path refused");
    require(succeeded(protocol::verifyAlgorithmExpansionPreserved(
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
      protocol::verifyAlgorithmExpansionPreserved, "algorithm-correspondence");
  negative(
      "wrong helper substitution", *source, *expanded,
      [&](ModuleOp module) {
        auto op = primitive(function(module, "both"), "bool.and");
        op->setOperand(1, op->getOperand(0));
      },
      protocol::verifyAlgorithmExpansionPreserved, "algorithm-correspondence");
  negative(
      "wrong local return", *source, *expanded,
      [&](ModuleOp module) {
        auto fn = function(module, "both");
        fn.getBody().front().back().setOperand(0, fn.getArgument(0));
      },
      protocol::verifyAlgorithmExpansionPreserved, "algorithm-correspondence");
  negative(
      "unused original helper changed", *source, *expanded,
      [&](ModuleOp module) {
        function(module, "identity")
            ->setAttr(
                "logical_origin",
                ArrayAttr::get(&context, {StringAttr::get(&context, "another"),
                                          ArrayAttr::get(&context, {})}));
      },
      protocol::verifyAlgorithmExpansionPreserved, "algorithm-correspondence");

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
        op->setOperand(1, op->getOperand(0));
      },
      protocol::verifyStoragePreserved, "storage-correspondence");

  negative(
      "existing release removed", *released, *released,
      [&](ModuleOp module) {
        plan::ReleaseOp selected;
        module.walk([&](plan::ReleaseOp op) { selected = op; });
        require(bool(selected), "missing existing release");
        selected.erase();
      },
      protocol::verifyStoragePreserved, "storage-correspondence");
  auto recipe = parseSourceFile<ModuleOp>(
      std::string(ZKC_MATH_FIXTURES) + "/iterated-sumcheck.mlir", &context);
  require(bool(recipe), "recipe fixture refused");
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
  recipeNegative("shape check made tautological", [&](ModuleOp module) {
    auto op = primitive(function(module, "init"), "index.equal");
    op->setOperand(1, op->getOperand(0));
  });
  recipeNegative("initial factors permuted", [&](ModuleOp module) {
    function(module, "init").walk([](local::VariantInjectOp op) {
      Value first = op->getOperand(1);
      op->setOperand(1, op->getOperand(2));
      op->setOperand(2, first);
    });
  });
  recipeNegative("fold uses wrong factor", [&](ModuleOp module) {
    auto fn = function(module, "bind");
    primitive(fn, "poly.fold", 1)
        ->setOperand(0, primitive(fn, "poly.fold")->getOperand(0));
  });
  recipeNegative("suffix pairing uses row twice", [&](ModuleOp module) {
    auto op = primitive(function(module, "round"), "index.add");
    op->setOperand(1, op->getOperand(0));
  });
  recipeNegative("coefficient convolution uses wrong factor",
                 [&](ModuleOp module) {
                   auto op = primitive(function(module, "round"), "field.mul");
                   op->setOperand(1, op->getOperand(0));
                 });
  recipeNegative("terminal state loses original prefix", [&](ModuleOp module) {
    auto fn = function(module, "finish");
    Value empty = primitive(fn, "poly.empty_point")->getResult(0);
    fn.walk([&](local::LocalYieldOp op) { op->setOperand(0, empty); });
  });
  recipeNegative("evaluation uses other factor", [&](ModuleOp module) {
    auto fn = function(module, "evaluate");
    primitive(fn, "poly.evaluate", 1)
        ->setOperand(0, primitive(fn, "poly.evaluate")->getOperand(0));
  });
  recipeNegative("shape guard moved after factor evaluation",
                 [&](ModuleOp module) {
                   auto fn = function(module, "evaluate");
                   primitive(fn, "control.require")
                       ->moveAfter(primitive(fn, "poly.evaluate"));
                 });
  return cases.result();
}
