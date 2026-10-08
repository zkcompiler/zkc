#include "../lib/Transforms/MathematicalSupport.h"
#include "mlir/Dialect/Tensor/IR/Tensor.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Program/Admission.h"
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
  require(pos != std::string::npos, "missing fixture edit");
  text.replace(pos, from.size(), to.str());
  return text;
}
OwningOpRef<ModuleOp> copy(ModuleOp module) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(module->clone()));
}
local::FuncOp realized(ModuleOp module) {
  local::FuncOp found;
  module.walk([&](local::FuncOp function) {
    if (function.getSymName() == "realized")
      found = function;
  });
  require(bool(found), "missing realized function");
  return found;
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
  auto source = parseSourceString<ModuleOp>(fixture, &context);
  require(bool(source), "realization fixture refused");
  auto expanded = copy(*source);
  require(succeeded(mathematical::expandMathRealizations(*expanded)),
          "realization failed");
  cases.run("polynomial intermediates disappear from realized execution", [&] {
    auto function = realized(*expanded);
    bool polynomial = false, kernel = false, dead = false;
    function.walk([&](Operation *op) {
      for (auto type : op->getResultTypes())
        polynomial |= isa<poly::PolynomialType>(type);
      kernel |= op->hasAttr("binding");
      dead |= op->hasAttr("binding") && op->getNumResults() && op->use_empty();
    });
    require(!dead, "unused total recipe became executable work");
    require(!polynomial && kernel,
            "formal data escaped or evaluation vanished");
    require(succeeded(mathematical::verifyMathRealizationsPreserved(*source,
                                                                    *expanded)),
            "containment failed");
  });
  for (bool simplify : {false, true})
    cases.run(
        simplify ? "full optimized pipeline" : "full unsimplified pipeline",
        [&] {
          auto module = copy(*source);
          PassManager manager(&context);
          manager.addPass(protocol::createProjectProtocolPass(simplify));
          manager.addPass(protocol::createEliminatePolynomialsPass());
          manager.addPass(protocol::createLowerMathPass());
          manager.addPass(protocol::createSelectPhysicalPass());
          require(succeeded(manager.run(*module)),
                  "realized program did not compile");
          bool residual = false;
          module->walk([&](Operation *op) {
            residual |= isa<local::RealizeOp, local::ApplyOp, func::FuncOp>(op);
          });
          require(!residual, "preparation construct escaped into execution");
        });
  auto refusal = [&](StringRef label, StringRef text, StringRef code,
                     bool prepare = false) {
    cases.run(label, [&] {
      bool named = false;
      ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
        named |= diagnostic.str().find(code.str()) != std::string::npos;
        return success();
      });
      auto module = parseSourceString<ModuleOp>(text, &context);
      if (prepare) {
        require(bool(module), "preparation fixture failed before preparation");
        require(failed(mathematical::expandMathRealizations(*module)),
                "invalid observation accepted");
      } else
        require(!module, "invalid realization admitted");
      require(named, "missing expected refusal identifier");
    });
  };
  refusal("missing helper", replace(fixture, "= @polynomial", "= @missing"),
          "local-realization-helper");
  refusal("ordered helper", replace(fixture, "= @polynomial", "= @work"),
          "local-realization-helper");
  refusal("wrong signature",
          replace(fixture,
                  "local.realize @realized = @polynomial : (!F,!F,!F)->!F",
                  "local.realize @realized = @polynomial : (!F,!F)->!F"),
          "local-realization-signature");
  refusal("extra realization attribute",
          replace(fixture, "= @polynomial :", "= @polynomial {extra=true} :"),
          "mathematical-formation");
  refusal("unused under-width observation",
          replace(fixture, "   %r = \"poly.evaluate\"",
                  "   %unused = \"poly.coefficients\"(%q) : (!P)->!A\n   %r = "
                  "\"poly.evaluate\""),
          "polynomial", true);
  refusal("non-protocol realization context",
          "module { func.func private @empty() {func.return} }",
          "local-realization-context", true);
  refusal("formal value at realization signature",
          replace(fixture, " local.realize @realized",
                  " func.func private @formal(%p:!P)->!P {func.return %p:!P}\n "
                  "local.realize @formal_exec = @formal : (!P)->!P\n "
                  "local.realize @realized"),
          "local-realization-signature");
  refusal("protocol call cannot bypass local application",
          replace(fixture, "callee=@work", "callee=@realized"),
          "interactive-symbol-kind");
  cases.run("multiple realizations and nested helpers", [&] {
    auto text = replace(fixture, " local.realize @realized", R"(
 func.func private @nested(%a:!F,%b:!F,%x:!F)->!F {
   %r=func.call @polynomial(%a,%b,%x):(!F,!F,!F)->!F
   func.return %r:!F
 }
 local.realize @second = @nested : (!F,!F,!F)->!F
 local.realize @realized)");
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "nested realization admission failed");
    require(succeeded(mathematical::expandMathRealizations(*module)),
            "nested realization expansion failed");
  });
  cases.run("independent helper recipe comparison", [&] {
    auto before = copy(*expanded);
    auto function = realized(*before);
    auto &block = function.getBody().front();
    while (!block.empty())
      block.back().erase();
    OpBuilder builder(&block, block.end());
    auto product = algebra::FieldMultiplyOp::create(
        builder, function.getLoc(), block.getArgument(0).getType(),
        block.getArgument(0), block.getArgument(1));
    local::ReturnOp::create(builder, function.getLoc(), product.getResult());
    auto unit = cast<protocol_ir::ProtocolModuleOp>(before->getBody()->front());
    auto candidate = copy(*before);
    auto after =
        cast<protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
    auto result = realized(*candidate);
    result.getBody().front().front().setAttr("site",
                                             builder.getStringAttr("product"));
    require(succeeded(mathematical::lowerCalculations(after, {result})),
            "direct recipe lowering failed");
    require(succeeded(
                mathematical::verifyCalculationRecipes(unit, after, {result})),
            "valid recipe comparison failed");
    result.getBody().front().front().setOperand(1, result.getArgument(0));
    bool named = false;
    ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
      named |= diagnostic.str().find("mathematical-lowering-preservation") !=
               std::string::npos;
      return success();
    });
    require(
        failed(mathematical::verifyCalculationRecipes(unit, after, {result})) &&
            named,
        "changed operand escaped independent recipe verification");
  });
  cases.run("static dimension discards unused tensor construction", [&] {
    auto text = replace(fixture, " local.realize @realized", R"(
 func.func private @dimension(%a:!F,%b:!F)->ui64 {
   %v = "tensor.from_elements"(%a,%b):(!F,!F)->!A
   %n = "data.dim"(%v){axis=0:i64}:(!A)->ui64
   func.return %n:ui64
 }
 local.realize @dimension_exec = @dimension : (!F,!F)->ui64
 local.realize @realized)");
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "dimension fixture refused");
    require(succeeded(mathematical::expandMathRealizations(*module)),
            "dimension realization failed");
    module->walk([&](local::FuncOp function) {
      if (function.getSymName() != "dimension_exec")
        return;
      auto &block = function.getBody().front();
      require(std::distance(block.begin(), block.end()) == 2,
              "static dimension emitted tensor construction");
      require(block.front().getName().getStringRef() ==
                  "algebra.exec.index_constant",
              "dimension is not a constant");
    });
  });
  cases.run("array recipe rejects shortened vector construction", [&] {
    auto before = copy(*expanded);
    auto function = realized(*before);
    auto &block = function.getBody().front();
    while (!block.empty())
      block.back().erase();
    OpBuilder builder(&block, block.end());
    auto array = tensor::FromElementsOp::create(
        builder, function.getLoc(),
        RankedTensorType::get({2}, block.getArgument(0).getType()),
        ValueRange{block.getArgument(0), block.getArgument(1)});
    auto at = algebra::ArrayAtOp::create(
        builder, function.getLoc(), block.getArgument(0).getType(),
        array.getResult(), builder.getI64IntegerAttr(1));
    local::ReturnOp::create(builder, function.getLoc(), at.getResult());
    auto candidate = copy(*before);
    auto result = realized(*candidate);
    auto unit = cast<protocol_ir::ProtocolModuleOp>(before->getBody()->front());
    auto after =
        cast<protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
    unsigned site = 0;
    for (auto &op : result.getBody().front().without_terminator())
      op.setAttr("site",
                 builder.getStringAttr("array_" + std::to_string(site++)));
    require(succeeded(mathematical::lowerCalculations(after, {result})),
            "array recipe failed");
    auto pristine = copy(*candidate);
    for (bool changeBinding : {false, true}) {
      auto mutated = copy(*pristine);
      auto changed = realized(*mutated);
      bool found = false;
      if (changeBinding)
        mutated->walk([&](local::OperationBindingOp binding) {
          if (binding.getContract() == "field_array.at") {
            binding->setAttr("arguments",
                             builder.getStrArrayAttr({"bls12-381.fr", "3"}));
            found = true;
          }
        });
      else
        changed.walk([&](Operation *op) {
          if (op->getName().getStringRef() == "algebra.exec.field_array_at") {
            op->setAttr("parameters", builder.getStrArrayAttr({"0"}));
            found = true;
          }
        });
      require(found, "array mutation target missing");
      ScopedDiagnosticHandler handler(&context,
                                      [](Diagnostic &) { return success(); });
      require(
          failed(mathematical::verifyCalculationRecipes(
              unit,
              cast<protocol_ir::ProtocolModuleOp>(mutated->getBody()->front()),
              {changed})),
          "changed array contract instance accepted");
    }
    Operation *append = nullptr;
    result.walk([&](Operation *op) {
      if (op->getName().getStringRef() == "algebra.exec.vector_append")
        append = op;
    });
    require(append, "array recipe did not append");
    append->getResult(0).replaceAllUsesWith(append->getOperand(0));
    append->erase();
    require(succeeded(verify(*candidate)), "short array mutation not formed");
    ScopedDiagnosticHandler handler(&context,
                                    [](Diagnostic &) { return success(); });
    require(
        failed(mathematical::verifyCalculationRecipes(unit, after, {result})),
        "short vector accepted by recipe comparison");
  });
  std::string large;
  large += " func.func private @leaf(%x:!F)->!F {\n";
  for (unsigned i = 0; i < 250; ++i)
    large +=
        "%v" + std::to_string(i) + " = algebra.field_add %x,%x : (!F,!F)->!F\n";
  large += "func.return %x:!F }\n func.func private @expanded(%x:!F)->!F {\n";
  for (unsigned i = 0; i < 220; ++i)
    large += "%v" + std::to_string(i) + " = func.call @leaf(%x):(!F)->!F\n";
  large +=
      "func.return %x:!F }\n local.realize @large1 = @expanded : (!F)->!F\n"
      "local.realize @large2 = @expanded : (!F)->!F\n local.realize @realized";
  refusal("shared realization expansion budget",
          replace(fixture, " local.realize @realized", large),
          "mathematical-analysis-limit");
  cases.run("conservative helper budget admits expandable bodies", [&] {
    auto smaller = large;
    for (unsigned i = 195; i < 220; ++i)
      smaller = replace(
          smaller,
          "%v" + std::to_string(i) + " = func.call @leaf(%x):(!F)->!F\n", "");
    auto module = parseSourceString<ModuleOp>(
        replace(fixture, " local.realize @realized", smaller), &context);
    require(bool(module), "bounded helper fixture refused");
    require(succeeded(mathematical::expandMathRealizations(*module)),
            "admitted conservative helper count failed expansion");
  });
  auto mutation = [&](StringRef label,
                      llvm::function_ref<void(ModuleOp)> change) {
    cases.run(label, [&] {
      auto candidate = copy(*expanded);
      change(*candidate);
      require(succeeded(verify(*candidate)), "mutation is not formed");
      bool named = false;
      ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
        named |= diagnostic.str().find("local-realization-correspondence") !=
                 std::string::npos;
        return success();
      });
      require(failed(mathematical::verifyMathRealizationsPreserved(
                  *source, *candidate)) &&
                  named,
              "containment accepted mutation");
    });
  };
  mutation("retained helper change", [&](ModuleOp module) {
    module.walk([](func::ReturnOp op) {
      op.setOperand(0, op->getBlock()->getArgument(0));
    });
  });
  mutation("partial runtime operation inserted", [&](ModuleOp module) {
    auto function = realized(module);
    auto *returned = &function.getBody().front().back();
    OpBuilder builder(function);
    local::OperationBindingOp::create(
        builder, function.getLoc(), "partial_inverse", "field.inverse",
        builder.getStrArrayAttr({"bls12-381.fr"}), "");
    builder.setInsertionPoint(returned);
    OperationState state(returned->getLoc(), "algebra.exec.field_inverse");
    state.addOperands(returned->getOperands());
    state.addTypes(returned->getOperandTypes());
    state.addAttribute("binding",
                       FlatSymbolRefAttr::get(&context, "partial_inverse"));
    state.addAttribute("parameters", builder.getArrayAttr({}));
    state.addAttribute("site", builder.getStringAttr("injected_inverse"));
    auto *inverse = builder.create(state);
    returned->setOperands(inverse->getResults());
  });
  mutation("explicit stop inserted", [&](ModuleOp module) {
    auto function = realized(module);
    auto *returned = &function.getBody().front().back();
    OpBuilder builder(returned);
    local::StopOp::create(builder, returned->getLoc(), "injected", "reject");
    returned->erase();
  });
  mutation("origin changed", [&](ModuleOp module) {
    realized(module)->setAttr(
        "logical_origin",
        ArrayAttr::get(&context, {StringAttr::get(&context, "unrelated"),
                                  ArrayAttr::get(&context, {})}));
  });
  mutation("unused binding inserted", [&](ModuleOp module) {
    Operation *binding = nullptr;
    module.walk([&](local::OperationBindingOp op) { binding = op; });
    require(binding, "no generated bindings");
    auto *extra = binding->clone();
    extra->setAttr("sym_name", StringAttr::get(&context, "extra"));
    binding->getBlock()->push_back(extra);
  });
  cases.run("internal signatures never enable ordinary source admission", [&] {
    program::LocalDefinitions empty;
    protocol::LocalRealization one{
        "realized", {"field:bls12-381.fr"}, {"field:bls12-381.fr"}};
    require(!protocol::admitNativeLocalDefinitions(empty, {one}),
            "valid internal signature refused");
    program::Function caller;
    caller.name = "caller";
    caller.arguments = {{"x", "field:bls12-381.fr"}};
    caller.results = {"field:bls12-381.fr"};
    caller.origin = program::LogicalOrigin{"caller", {}};
    caller.body =
        program::Body{{"invoke", program::LocalApply{"realized", {"x"}, {"r"}}},
                      {"", program::Return{{"r"}}}};
    program::LocalDefinitions calls;
    calls.functions.push_back(std::move(caller));
    require(!protocol::admitNativeLocalDefinitions(calls, {one}),
            "explicit internal realization signature was not resolved");
    auto ordinary = protocol::admitNativeLocalDefinitions(calls);
    require(bool(ordinary), "ordinary admission accepted an unresolved call");
    require(llvm::toString(std::move(ordinary)).find("algorithm-call-symbol") !=
                std::string::npos,
            "wrong unresolved ordinary call refusal");
    auto duplicate = protocol::admitNativeLocalDefinitions(empty, {one, one});
    require(bool(duplicate), "duplicate internal signature admitted");
    require(
        llvm::toString(std::move(duplicate)).find("local-realization-symbol") !=
            std::string::npos,
        "wrong signature collision refusal");
    one.inputs = {"polynomial:bls12-381.fr"};
    auto invalid = protocol::admitNativeLocalDefinitions(empty, {one});
    require(bool(invalid), "non-total runtime data admitted");
    require(llvm::toString(std::move(invalid))
                    .find("local-realization-signature") != std::string::npos,
            "wrong data-only refusal");
  });
  cases.run("realization signatures share a policy work limit", [&] {
    program::LocalDefinitions empty;
    std::vector<protocol::LocalRealization> signatures;
    for (unsigned i = 0; i < 100; ++i)
      signatures.push_back(
          {"realization_" + std::to_string(i),
           std::vector<std::string>(1024, "field:bls12-381.fr"),
           std::vector<std::string>(1024, "field:bls12-381.fr")});
    auto refused = protocol::admitNativeLocalDefinitions(empty, signatures);
    require(bool(refused), "shared policy work ceiling was ignored");
    require(
        llvm::toString(std::move(refused)).find("local-realization-limit") !=
            std::string::npos,
        "wrong realization policy limit refusal");
  });
  return cases.result();
}
