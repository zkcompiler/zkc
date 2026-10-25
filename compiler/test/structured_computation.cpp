#include "mlir/Dialect/Linalg/IR/Linalg.h"
#include "mlir/Dialect/Tensor/IR/Tensor.h"
#include "mlir/IR/Diagnostics.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Transforms/StructuredComputation.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::mathematical;
int main() {
  test::Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto source = parseSourceString<ModuleOp>(R"(
    module {
      func.func @formula(%x: !algebra.field<"koala-bear">,
                         %y: !algebra.field<"koala-bear">,
                         %c: !algebra.field<"koala-bear">) -> !algebra.field<"koala-bear"> {
        %a = "algebra.field_multiply"(%x, %y) : (!algebra.field<"koala-bear">, !algebra.field<"koala-bear">) -> !algebra.field<"koala-bear">
        %b = "algebra.field_multiply"(%x, %y) : (!algebra.field<"koala-bear">, !algebra.field<"koala-bear">) -> !algebra.field<"koala-bear">
        %s = "algebra.field_add"(%a, %b) : (!algebra.field<"koala-bear">, !algebra.field<"koala-bear">) -> !algebra.field<"koala-bear">
        %r = "algebra.field_add"(%s, %c) : (!algebra.field<"koala-bear">, !algebra.field<"koala-bear">) -> !algebra.field<"koala-bear">
        return %r : !algebra.field<"koala-bear">
      }
    })",
                                            &context);
  test::require(bool(source), "source parsing");
  auto formula = *source->getOps<func::FuncOp>().begin();
  const bool rowwise[] = {true, true, false};
  for (auto kind : {StructuredResult::Map, StructuredResult::Sum}) {
    for (StringRef formulaKind : {"identity", "broadcast", "constant"}) {
      cases.run(
          (formulaKind + (kind == StructuredResult::Map ? " map" : " sum"))
              .str(),
          [&] {
            OwningOpRef<func::FuncOp> simple(func::FuncOp::create(
                formula.getLoc(), "simple", formula.getFunctionType()));
            auto *block = simple->addEntryBlock();
            OpBuilder builder(block, block->end());
            Value returned =
                block->getArgument(formulaKind == "identity" ? 0 : 2);
            if (formulaKind == "constant")
              returned = algebra::ConstantFieldOp::create(
                  builder, formula.getLoc(), returned.getType(), "42");
            func::ReturnOp::create(builder, formula.getLoc(), returned);
            auto candidate =
                proposeStructuredComputation(*block, rowwise, kind);
            test::require(bool(candidate), "simple proposal");
            test::require(succeeded(verifyStructuredComputation(
                              *block, rowwise, kind, *candidate)),
                          "simple original correspondence");
            test::require(succeeded(optimizeStructuredComputation(*candidate)),
                          "simple optimization");
            test::require(bool(consumeStructuredComputation(*block, rowwise,
                                                            kind, *candidate)),
                          "simple candidate consumption");
          });
    }
    cases.run(
        kind == StructuredResult::Map ? "map CSE and consumption"
                                      : "sum CSE and consumption",
        [&] {
          auto candidate =
              proposeStructuredComputation(formula.front(), rowwise, kind);
          test::require(bool(candidate), "proposal");
          test::require(succeeded(verifyStructuredComputation(
                            formula.front(), rowwise, kind, *candidate)),
                        "original correspondence");
          unsigned before = 0, after = 0, stagesBefore = 0, stagesAfter = 0;
          candidate->walk([&](algebra::FieldMultiplyOp) { ++before; });
          candidate->walk([&](linalg::GenericOp) { ++stagesBefore; });
          test::require(succeeded(optimizeStructuredComputation(*candidate)),
                        "CSE");
          candidate->walk([&](algebra::FieldMultiplyOp) { ++after; });
          candidate->walk([&](linalg::GenericOp) { ++stagesAfter; });
          test::require(stagesBefore ==
                                (kind == StructuredResult::Map ? 1 : 2) &&
                            stagesAfter == 1,
                        "upstream fusion did not combine map and reduction");
          test::require(before == 2 && after == 1,
                        "upstream CSE did not share multiplication");
          auto actual = consumeStructuredComputation(formula.front(), rowwise,
                                                     kind, *candidate);
          test::require(bool(actual), "actual candidate consumption");
        });
    auto mutation = [&](StringRef name, auto change) {
      for (bool optimized : {false, true}) {
        cases.run(
            (name + (optimized ? " after fusion" : " before fusion")).str(),
            [&] {
              auto candidate =
                  proposeStructuredComputation(formula.front(), rowwise, kind);
              test::require(bool(candidate), "proposal");
              if (optimized)
                test::require(
                    succeeded(optimizeStructuredComputation(*candidate)),
                    "upstream optimization");
              change(*candidate);
              std::string diagnostic;
              ScopedDiagnosticHandler handler(&context, [&](Diagnostic &d) {
                diagnostic += d.str();
                return success();
              });
              test::require(failed(verifyStructuredComputation(
                                formula.front(), rowwise, kind, *candidate)),
                            "mutation accepted");
              test::require(diagnostic.find("structured-computation") !=
                                std::string::npos,
                            "missing refusal identifier");
            });
      }
    };
    mutation("actual input permutation", [&](ModuleOp module) {
      module.walk([&](linalg::GenericOp generic) {
        if (generic.getInputs().size() < 2)
          return;
        Value a = generic.getOperand(0), b = generic.getOperand(1);
        generic->setOperand(0, b);
        generic->setOperand(1, a);
      });
    });
    mutation("actual scalar mutation after checking", [&](ModuleOp module) {
      test::require(succeeded(verifyStructuredComputation(
                        formula.front(), rowwise, kind, module)),
                    "precondition");
      module.walk([&](algebra::FieldMultiplyOp op) {
        op->setOperand(1, op.getOperand(0));
      });
    });
    mutation("changed iteration kind", [&](ModuleOp module) {
      module.walk([&](linalg::GenericOp generic) {
        generic.setIteratorTypesAttr(ArrayAttr::get(
            &context, {linalg::IteratorTypeAttr::get(
                          &context, kind == StructuredResult::Map
                                        ? utils::IteratorType::reduction
                                        : utils::IteratorType::parallel)}));
      });
    });
    mutation("unknown scalar attribute", [&](ModuleOp module) {
      module.walk([&](algebra::FieldMultiplyOp op) {
        op->setAttr("meaning", UnitAttr::get(&context));
      });
    });
    mutation("nested region in scalar packet", [&](ModuleOp module) {
      auto function = *module.getOps<func::FuncOp>().begin();
      OpBuilder builder(&function.front().back());
      auto nested = ModuleOp::create(builder, function.getLoc());
      builder.setInsertionPointToEnd(nested.getBody());
      ModuleOp::create(builder, function.getLoc());
    });
    mutation("unlisted scalar capture", [&](ModuleOp module) {
      module.walk([&](linalg::GenericOp generic) {
        auto outer = generic->getParentOfType<func::FuncOp>();
        auto &body = generic.getRegion().front();
        if (generic.getInputs().size() < 3)
          return;
        body.getArgument(2).replaceAllUsesWith(outer.getArgument(2));
      });
    });
    mutation(
        "returned value disconnected from computation", [&](ModuleOp module) {
          auto function = *module.getOps<func::FuncOp>().begin();
          function.front().back().setOperand(
              0, function.getArgument(kind == StructuredResult::Map ? 0 : 2));
        });
    mutation("changed tensor coordinate", [&](ModuleOp module) {
      module.walk([&](linalg::GenericOp generic) {
        auto maps = generic.getIndexingMapsArray();
        maps[0] = AffineMap::get(1, 0, getAffineConstantExpr(0, &context));
        SmallVector<Attribute> attrs;
        for (auto map : maps)
          attrs.push_back(AffineMapAttr::get(map));
        generic.setIndexingMapsAttr(ArrayAttr::get(&context, attrs));
      });
    });
    if (kind == StructuredResult::Sum) {
      mutation("nonzero empty reduction seed", [&](ModuleOp module) {
        module.walk([&](algebra::ConstantFieldOp op) { op.setValue("1"); });
      });
      mutation("reduction omits accumulator", [&](ModuleOp module) {
        module.walk([&](linalg::GenericOp generic) {
          if (generic.getIteratorTypesArray().front() !=
              utils::IteratorType::reduction)
            return;
          auto &body = generic.getRegion().front();
          auto add =
              body.back().getOperand(0).getDefiningOp<algebra::FieldAddOp>();
          body.back().setOperand(0, add.getOperand(1));
          add.erase();
        });
      });
    } else {
      mutation("uninitialized output read", [&](ModuleOp module) {
        module.walk([&](linalg::GenericOp generic) {
          auto &body = generic.getRegion().front();
          body.back().setOperand(0, body.getArguments().back());
        });
      });
      mutation("different tensor extent binding", [&](ModuleOp module) {
        module.walk([&](tensor::DimOp dim) {
          auto function = dim->getParentOfType<func::FuncOp>();
          dim->setOperand(0, function.getArgument(1));
        });
      });
    }
  }
  return cases.result();
}
