#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/ComputationRecipes.h"
#include "support/ScopedFinite.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Interfaces/Mathematical.h"
#include <iterator>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
constexpr llvm::StringLiteral fixture = R"mlir(
module @words attributes {exec.computation} {
  func.func private @word(%a:ui64,%b:ui64,%choose:i1)->(ui64,ui64,ui64,ui64,ui64) {
    %sum = "data.index_wrapping_add"(%a,%b) : (ui64,ui64)->ui64
    %difference = "data.index_wrapping_subtract"(%a,%b) : (ui64,ui64)->ui64
    %bits = "data.index_bit_and"(%a,%b) : (ui64,ui64)->ui64
    %shift = "data.index_logical_shift_right"(%a,%b) : (ui64,ui64)->ui64
    %unused = "data.index_bit_and"(%b,%b) : (ui64,ui64)->ui64
    %selected = arith.select %choose,%sum,%difference : ui64
    return %sum,%difference,%bits,%shift,%selected : ui64,ui64,ui64,ui64,ui64
  }
  func.func @entry(%a:ui64,%b:ui64,%choose:i1)->(ui64,ui64,ui64,ui64,ui64) {
    %v:5 = call @word(%a,%b,%choose) : (ui64,ui64,i1)->(ui64,ui64,ui64,ui64,ui64)
    return %v#0,%v#1,%v#2,%v#3,%v#4 : ui64,ui64,ui64,ui64,ui64
  }
}
)mlir";
constexpr llvm::StringLiteral contracts[] = {
    "index.wrapping_add", "index.wrapping_sub", "index.bit_and",
    "index.logical_shift_right"};
constexpr MathematicalIdentity identities[] = {
    MathematicalIdentity::IndexWrappingAdd,
    MathematicalIdentity::IndexWrappingSubtract,
    MathematicalIdentity::IndexBitAnd,
    MathematicalIdentity::IndexLogicalShiftRight};

OwningOpRef<ModuleOp> parse(MLIRContext &context) {
  auto source = parseSourceString<ModuleOp>(fixture, &context);
  require(source && succeeded(admitStage(*source)) &&
              succeeded(mathematical::verifyComputationUnit(*source)),
          "total index computation failed native admission");
  return source;
}

void mismatch(ModuleOp source, ModuleOp candidate) {
  finite::VerificationResult result{finite::VerificationStatus::Verified, {}};
  ScopedDiagnosticHandler silence(source.getContext(),
                                  [](Diagnostic &) { return success(); });
  require(failed(computation::verifyEntryRecipes(source, candidate, "words", {},
                                                 {}, &result)) &&
              result.status == finite::VerificationStatus::Mismatch,
          "recipe reader accepted a changed word recipe");
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run("exact word identities, dependencies and attribute refusal", [&] {
    auto source = parse(context);
    auto helper = SymbolTable(*source).lookup<func::FuncOp>("word");
    unsigned index = 0;
    for (auto &op : helper.front().without_terminator()) {
      auto model = dyn_cast<MathematicalOpInterface>(&op);
      require(bool(model), "word operation has no mathematical interface");
      auto expected = index < 4    ? identities[index]
                      : index == 4 ? MathematicalIdentity::IndexBitAnd
                                   : MathematicalIdentity::Select;
      require(model.getMathematicalIdentity() == expected &&
                  succeeded(mathematical::verifyOperation(
                      &op, mathematical::Context::Helper)),
              "word identity or formation differs");
      auto dependencies = model.getOperandDependencies(0);
      require(dependencies.size() == op.getNumOperands(),
              "missing word dependency");
      for (unsigned i = 0; i < dependencies.size(); ++i)
        require(dependencies[i] == i, "word dependency order differs");
      require(model.getOperandDependencies(1).empty(),
              "nonexistent word result has dependencies");
      OpBuilder builder(&context);
      op.setAttr("overflow", builder.getStringAttr("poison"));
      bool diagnosed = false;
      {
        ScopedDiagnosticHandler handler(&context, [&](Diagnostic &d) {
          diagnosed |=
              d.str().find("mathematical-formation") != std::string::npos;
          return success();
        });
        require(failed(mathematical::verifyOperation(
                    &op, mathematical::Context::Helper)) &&
                    diagnosed,
                "word operation admitted an extra attribute");
      }
      op.removeAttr("overflow");
      ++index;
    }
    require(index == 6, "word fixture lost an operation");
  });
  cases.run("closure and exact readback retain every word operation", [&] {
    auto source = parse(context);
    auto entry = mathematical::getComputationEntry(*source);
    uint64_t remaining = 1000000;
    auto closed = computation::closeComputation(entry, remaining);
    require(closed &&
                succeeded(computation::verifyDependencies(*source, *closed)),
            "word closure did not preserve its helper");
    auto snapshot = computation::exactReadback(entry, *source, remaining);
    require(bool(snapshot), "word helper readback failed");
    unsigned count = 0;
    snapshot->walk([&](Operation *op) {
      count += isa<data::IndexWrappingAddOp, data::IndexWrappingSubtractOp,
                   data::IndexBitAndOp, data::IndexLogicalShiftRightOp>(op);
    });
    require(count == 5, "word readback dropped dormant work");
  });
  cases.run("word signatures and selection refuse other integer carriers", [&] {
    for (StringRef type : {"i64", "ui32", "si64"}) {
      auto text = (Twine("module {func.func @bad(%a:") + type + ",%b:" + type +
                   ") { %v = \"data.index_wrapping_add\"(%a,%b) : (" + type +
                   "," + type + ")->" + type + " return }}")
                      .str();
      auto source =
          parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
      require(bool(source), "malformed-carrier fixture did not parse");
      ScopedDiagnosticHandler silence(&context,
                                      [](Diagnostic &) { return success(); });
      require(failed(verify(*source)),
              "word operation accepted another integer carrier");
    }
    auto source = parseSourceString<ModuleOp>(R"(
      module {func.func @bad(%a:i64,%b:i64,%c:i1) {
        %v = arith.select %c,%a,%b : i64
        return
      }}
    )",
                                              &context);
    require(bool(source), "signless-selection fixture failed formation");
    source->walk([&](arith::SelectOp select) {
      auto model = cast<MathematicalOpInterface>(select.getOperation());
      require(!model.getMathematicalIdentity(),
              "selection admitted a signless index carrier");
    });
  });
  cases.run(
      "word recipes and ui64 selection survive independent comparison", [&] {
        auto closure = parse(context);
        // Recipe selection consumes the checked, expanded entry. The earlier
        // readback case separately covers calls and the complete helper closure.
        auto source = computationRecipeSource(*closure, "word", "lowered_entry");
        auto before = scopedFinite::clone(*source);
        mathematical::RealizationWork work;
        auto output = realizeComputationEntry(*source, "words", {}, work);
        require(output && succeeded(computation::verifyRecipeOutput(*output)) &&
                    succeeded(computation::verifyEntryRecipes(*source, *output,
                                                              "words")),
                "total word recipe failed independent validation");
        auto owner = computationRecipeOutput(*output);
        require(scopedFinite::applications(owner).size() == 5,
                "word recipe lost unused arithmetic or changed its expansion");
        require(OperationEquivalence::isEquivalentTo(
                    *source, *before, OperationEquivalence::IgnoreLocations),
                "word recipe production mutated its mathematical source");
        for (unsigned i = 0; i < std::size(contracts); ++i) {
          for (StringRef mutation : {"contract", "implementation", "operand",
                                     "parameters", "site"}) {
            auto candidate = scopedFinite::clone(*output);
            auto apply = scopedFinite::application(
                computationRecipeOutput(*candidate), contracts[i]);
            OpBuilder builder(&context);
            if (mutation == "contract" || mutation == "implementation") {
              auto binding =
                  SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
                      apply, apply.getBindingAttr());
              auto other = contracts[(i + 1) % std::size(contracts)];
              if (mutation == "contract")
                binding->setAttr("contract", builder.getStringAttr(other));
              else
                binding->setAttr("implementation",
                                 builder.getStringAttr("native/" + other));
            } else if (mutation == "operand")
              apply->setOperand(2, apply.getInputs()[0]);
            else if (mutation == "parameters")
              apply->setAttr("parameters", builder.getArrayAttr(
                                               {builder.getI64IntegerAttr(1)}));
            else
              apply->setAttr("site", builder.getStringAttr("changed"));
            if (mutation == "contract" || mutation == "operand" ||
                mutation == "site")
              require(succeeded(verify(*candidate)),
                      "recipe mutation lost native formation");
            mismatch(*source, *candidate);
          }
        }
        auto candidate = scopedFinite::clone(*output);
        bool changed = false;
        candidate->walk([&](exec::CompleteOp returned) {
          auto function = returned->getParentOfType<func::FuncOp>();
          if (!changed && function->hasAttr("runtime.region") &&
              function.getNumArguments() == 3 &&
              returned.getValues().size() == 1) {
            // Both captured alternatives are ui64; selecting the other argument
            // preserves native formation while changing the source mathematics.
            returned->setOperand(
                1, function.getArgument(
                       returned.getValues()[0] == function.getArgument(1) ? 2
                                                                          : 1));
            changed = true;
          }
        });
        require(changed && succeeded(verify(*candidate)),
                "selection mutation lost native formation");
        mismatch(*source, *candidate);
      });
  return cases.result();
}
