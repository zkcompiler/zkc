#include "mlir/AsmParser/AsmParser.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/KernelRecipes.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Dialect/Registry.h"

using namespace mlir;
using namespace llvm;
using namespace zkc;
using zkc::test::require;
namespace {
template <class T> T take(Expected<T> value) {
  if (!value) {
    errs() << toString(value.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*value);
}
Operation *first(Operation *owner, StringRef name) {
  Operation *result = nullptr;
  owner->walk([&](Operation *op) {
    if (!result && op->getName().getStringRef() == name)
      result = op;
  });
  require(result, "missing mutation target");
  return result;
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  zkc::test::Cases cases;
  for (StringRef invalid :
       {"!algebra.quotient<1,4>", "!algebra.quotient<17,0>"})
    cases.run("invalid native quotient type parameters", [&] {
      ScopedDiagnosticHandler quiet(&context,
                                    [](Diagnostic &) { return success(); });
      require(!parseType(invalid, &context), "invalid quotient type admitted");
    });
  cases.run("formal quotient cannot be a numerical entry port", [&] {
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    auto invalid = parseSourceString<ModuleOp>(R"mlir(
      module { kernel.module @bad {
        func.func @entry(%x:!algebra.quotient<17,4>)->!algebra.quotient<17,4> {
          return %x : !algebra.quotient<17,4>
        }
      } })mlir",
                                               &context);
    require(!invalid, "formal quotient escaped through numerical entry ports");
  });
  auto source = parseSourceString<ModuleOp>(R"mlir(
    !R = !algebra.quotient<17,4>
    !I = !algebra.indices
    module {
      func.func private @calculate(%a:!I,%b:!I)->!I {
        %x = algebra.quotient_project %a : (!I)->!R
        %y = algebra.quotient_project %b : (!I)->!R
        %z = algebra.quotient_subtract %x,%y : (!R,!R)->!R
        %v = algebra.quotient_multiply %z,%x : (!R,!R)->!R
        %r = algebra.quotient_coefficients %v : (!R)->!I
        return %r : !I
      }
    })mlir",
                                            &context);
  require(bool(source), "quotient source admission failed");
  auto unit = zkc::test::kernelRecipeSource(*source, "calculate", "entry");
  auto snapshot =
      OwningOpRef<kernel::ModuleOp>(cast<kernel::ModuleOp>(unit->clone()));
  mathematical::RealizationWork work;
  auto candidate = zkc::test::realizeKernelEntry(*unit, "quotient", {}, work);
  cases.run("managed coefficient realization and immutable source", [&] {
    require(bool(candidate), "quotient recipe failed");
    require(
        succeeded(kernel::verifyEntryRecipes(*unit, *candidate, "quotient")),
        "independent quotient recipe reader failed");
    require(OperationEquivalence::isEquivalentTo(
                *unit, *snapshot, OperationEquivalence::IgnoreLocations),
            "source mutated during realization");
    candidate->walk([&](Operation *op) {
      for (Type type : op->getResultTypes())
        require(!isa<algebra::QuotientType>(type),
                "formal type escaped into native execution");
    });
  });
  for (StringRef mutation : {"modulus", "degree", "operand", "return", "site",
                             "contract", "implementation"})
    cases.run(mutation, [&] {
      require(bool(candidate), "missing candidate");
      auto changed = OwningOpRef<ModuleOp>(cast<ModuleOp>(candidate->clone()));
      OpBuilder builder(&context);
      auto *project = first(*changed, "algebra.exec.quotient_project");
      auto *product = first(*changed, "algebra.exec.quotient_multiply");
      if (mutation == "modulus" || mutation == "degree") {
        auto *constant =
            project->getOperand(mutation == "modulus" ? 1 : 2).getDefiningOp();
        constant->setAttr(
            "parameters",
            builder.getStrArrayAttr({mutation == "modulus" ? "19" : "8"}));
      } else if (mutation == "operand") {
        product->setOperand(0, product->getOperand(1));
      } else if (mutation == "return") {
        first(*changed, "local.return")->setOperand(0, project->getResult(0));
      } else if (mutation == "site") {
        product->setAttr("site", builder.getStringAttr("unrelated"));
      } else {
        auto owner = zkc::test::kernelRecipeOutput(*changed);
        auto binding = SymbolTable(owner).lookup<local::OperationBindingOp>(
            product->getAttrOfType<FlatSymbolRefAttr>("binding").getValue());
        if (mutation == "contract") {
          auto *difference = first(*changed, "algebra.exec.quotient_subtract");
          product->setAttr("binding", difference->getAttr("binding"));
        } else {
          binding.setImplementation("native/quotient.multiply");
        }
      }
      ScopedDiagnosticHandler quiet(&context,
                                    [](Diagnostic &) { return success(); });
      require(failed(kernel::verifyEntryRecipes(*unit, *changed, "quotient")),
              "altered recipe accepted");
    });
  cases.run("source identity binds quotient operations", [&] {
    using namespace language;
    auto captured = take(capture({{"sample", R"(
      module sample;
      type I=builtin("indices");
      math fn calculate(a:I,b:I)->I {
        let x=intrinsic<17,4>("quotient.value.project",a);
        let y=intrinsic<17,4>("quotient.value.project",b);
        let z=intrinsic<17,4>("quotient.value.subtract",x,y);
        return intrinsic<17,4>("quotient.value.coefficients",z);
      }
      protocol Run roles(P)(a:I@P,b:I@P)->(r:I@P){return calculate(a,b);}
      entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}
    )",
                                   "quotient.zkc"}}));
    auto checked = take(analyze(std::move(captured)).checkedProject());
    auto original = take(prepareOriginal(
        take(zkc::test::closeProtocolDeployment(checked, "sample::Demo"))));
    for (bool simplify : {false, true})
      take(compileEntry(original, {simplify, false}));
    auto module = parseSourceString<ModuleOp>(original.bytes(), &context);
    require(bool(module), "source original did not parse");
    auto *subtract = first(*module, "algebra.quotient_subtract");
    OpBuilder builder(subtract);
    OperationState state(subtract->getLoc(), "algebra.quotient_add");
    state.addTypes(subtract->getResultTypes());
    state.addOperands(subtract->getOperands());
    auto *add = builder.create(state);
    subtract->replaceAllUsesWith(add);
    subtract->erase();
    require(succeeded(verify(*module)),
            "same-type mutation must remain well formed");
    auto comparison = compareOriginal(original.entry(), *module);
    require(!comparison, "changed source operation accepted");
    require(StringRef(toString(comparison.takeError()))
                .contains("source.correspondence"),
            "unexpected source identity diagnostic");
  });
  return cases.result();
}
