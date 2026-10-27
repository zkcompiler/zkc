#include "mlir/AsmParser/AsmParser.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/ComputationRecipes.h"
#include "support/ProtocolDeployment.h"
#include "support/ScopedComputation.h"
#include "support/ScopedFinite.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"

using namespace mlir;
using namespace llvm;
using namespace zkc;
using zkc::test::require;
namespace sf = zkc::test::scopedFinite;
namespace sc = zkc::test::scopedComputation;
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
  for (StringRef invalid : {"!poly.quotient<1,4>", "!poly.quotient<17,0>"})
    cases.run("invalid native quotient type parameters", [&] {
      ScopedDiagnosticHandler quiet(&context,
                                    [](Diagnostic &) { return success(); });
      require(!parseType(invalid, &context), "invalid quotient type admitted");
    });
  cases.run("formal quotient cannot be a numerical entry port", [&] {
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    auto invalid = parseSourceString<ModuleOp>(R"mlir(
      module { module @bad attributes {exec.computation} {
        func.func @entry(%x:!poly.quotient<17,4>)->!poly.quotient<17,4> {
          return %x : !poly.quotient<17,4>
        }
      } })mlir",
                                               &context);
    require(bool(invalid),
            "standard computation module is structurally malformed");
    auto unit = cast<ModuleOp>(invalid->getBody()->front());
    require(failed(mathematical::verifyComputationUnit(unit)),
            "formal quotient escaped through numerical entry ports");
  });
  for (StringRef wrong : {"!poly.quotient<19,4>", "!poly.quotient<17,8>"})
    cases.run("quotient binary requires exact modulus and degree", [&] {
      ScopedDiagnosticHandler quiet(&context,
                                    [](Diagnostic &) { return success(); });
      auto text =
          (Twine(
               "module { func.func private @bad(%a:!poly.quotient<17,4>,%b:") +
           wrong +
           ")->!poly.quotient<17,4> { %r = poly.quotient_multiply %a,%b : " +
           "(!poly.quotient<17,4>," + wrong + ")->!poly.quotient<17,4> " +
           "return %r : !poly.quotient<17,4> } }")
              .str();
      require(!parseSourceString<ModuleOp>(text, &context),
              "mismatched quotient rings admitted");
    });
  auto source = parseSourceString<ModuleOp>(R"mlir(
    !R = !poly.quotient<17,4>
    !I = !algebra.indices
    module {
      func.func private @calculate(%a:!I,%b:!I)->!I {
        %x = poly.quotient_project %a : (!I)->!R
        %y = poly.quotient_project %b : (!I)->!R
        %z = poly.quotient_subtract %x,%y : (!R,!R)->!R
        %v = poly.quotient_multiply %z,%x : (!R,!R)->!R
        %r = poly.quotient_coefficients %v : (!R)->!I
        return %r : !I
      }
    })mlir",
                                            &context);
  require(bool(source), "quotient source admission failed");
  auto unit = zkc::test::computationRecipeSource(*source, "calculate", "entry");
  auto snapshot =
      OwningOpRef<mlir::ModuleOp>(cast<mlir::ModuleOp>(unit->clone()));
  mathematical::RealizationWork work;
  auto candidate =
      zkc::test::realizeComputationEntry(*unit, "quotient", {}, work);
  cases.run("managed coefficient realization and immutable source", [&] {
    require(bool(candidate), "quotient recipe failed");
    require(succeeded(
                computation::verifyEntryRecipes(*unit, *candidate, "quotient")),
            "independent quotient recipe reader failed");
    require(OperationEquivalence::isEquivalentTo(
                *unit, *snapshot, OperationEquivalence::IgnoreLocations),
            "source mutated during realization");
    candidate->walk([&](Operation *op) {
      for (Type type : op->getResultTypes())
        require(!isa<poly::QuotientType>(type),
                "formal type escaped into native execution");
    });
  });
  for (StringRef mutation : {"modulus", "degree", "operand", "return", "site",
                             "contract", "implementation"})
    cases.run(mutation, [&] {
      require(bool(candidate), "missing candidate");
      auto changed = OwningOpRef<ModuleOp>(cast<ModuleOp>(candidate->clone()));
      OpBuilder builder(&context);
      auto project = sf::application(*changed, "quotient.project");
      auto product = sf::application(*changed, "quotient.multiply");
      if (mutation == "modulus" || mutation == "degree") {
        auto value = project.getInputs()[mutation == "modulus" ? 1 : 2];
        exec::ApplyOp constant;
        for (auto op : sf::applications(*changed, "index.constant"))
          if (sc::payload(op).front() == value)
            constant = op;
        require(bool(constant), "missing quotient parameter producer");
        constant->setAttr(
            "parameters",
            builder.getStrArrayAttr({mutation == "modulus" ? "19" : "8"}));
      } else if (mutation == "operand") {
        product.getInputsMutable()[0].set(product.getInputs()[1]);
      } else if (mutation == "return") {
        first(*changed, "exec.returned")
            ->setOperand(0, sc::payload(project).front());
      } else if (mutation == "site") {
        product->setAttr("site", builder.getStringAttr("unrelated"));
      } else {
        auto owner = zkc::test::computationRecipeOutput(*changed);
        auto binding = SymbolTable(owner).lookup<runtime::BindingOp>(
            product->getAttrOfType<FlatSymbolRefAttr>("binding").getValue());
        if (mutation == "contract") {
          auto difference = sf::application(*changed, "quotient.subtract");
          product->setAttr("binding", difference->getAttr("binding"));
        } else {
          binding.setImplementation("native/quotient.multiply");
        }
      }
      ScopedDiagnosticHandler quiet(&context,
                                    [](Diagnostic &) { return success(); });
      require(succeeded(verify(*changed)), "quotient mutation lost formation");
      require(
          failed(computation::verifyEntryRecipes(*unit, *changed, "quotient")),
          "altered recipe accepted");
    });
  cases.run(
      "upstream select does not widen the admitted mathematical profile", [&] {
        auto choices = parseSourceString<ModuleOp>(R"mlir(
      !R = !poly.quotient<17,4>
      !I = !algebra.indices
      module {
        func.func private @choose(%flag:i1,%a:!I,%b:!I)->!I {
          %x = poly.quotient_project %a : (!I)->!R
          %y = poly.quotient_project %b : (!I)->!R
          %choice = arith.select %flag,%x,%y : !R
          %r = poly.quotient_coefficients %choice : (!R)->!I
          return %r : !I
        }
      })mlir",
                                                   &context);
        require(bool(choices), "formal selection did not form");
        auto selected =
            zkc::test::computationRecipeSource(*choices, "choose", "entry");
        ScopedDiagnosticHandler quiet(&context,
                                      [](Diagnostic &) { return success(); });
        require(
            succeeded(verify(*selected)) &&
                failed(mathematical::verifyComputationUnit(*selected)),
            "upstream structural legality widened the scalar select profile");
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
    auto *subtract = first(*module, "poly.quotient_subtract");
    OpBuilder builder(subtract);
    OperationState state(subtract->getLoc(), "poly.quotient_add");
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
