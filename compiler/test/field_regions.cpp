#include "../lib/Transforms/FieldRegion.h"
#include "../lib/Transforms/LaneRealization.h"
#include "../lib/Transforms/MathematicalRecipes.h"
#include "mlir/Dialect/Linalg/IR/Linalg.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Registry.h"

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::mathematical;
using namespace zkc::test;
namespace {
std::string sourceText(StringRef field) {
  return ("!F = !algebra.field<\"" + field + "\">\n" +
          "!V = !algebra.field_vector<\"" + field + "\">\n" + R"mlir(
module {
 func.func @formula(%x:!F,%a:!F,%unused:!F)->!F {
   %first = algebra.field_multiply %x,%a : (!F,!F)->!F
   %second = algebra.field_multiply %x,%a : (!F,!F)->!F
   %sum = algebra.field_add %first,%second : (!F,!F)->!F
   %out = algebra.field_subtract %sum,%a : (!F,!F)->!F
   func.return %out : !F
 }
 func.func @bindings(%x:!V,%a:!F,%unused:!V,%rows:ui64)->!V {
   func.return %x : !V
 }
})mlir")
      .str();
}
linalg::GenericOp payload(ModuleOp module) {
  auto function = *module.getOps<func::FuncOp>().begin();
  return *function.getOps<linalg::GenericOp>().begin();
}

} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry, MLIRContext::Threading::DISABLED);
  context.loadAllAvailableDialects();
  Cases cases;
  for (StringRef field :
       {"bls12-381.fr", "bn254.fr", "ristretto255.scalar", "koala-bear",
        "koala-bear.ext4-binomial3", "koala-bear.ext8-binomial3",
        "gf2-64.pentanomial-4-3-1",
        "gf2-64.pentanomial-4-3-1.ext3-trinomial1"}) {
    auto source = parseSourceString<ModuleOp>(sourceText(field), &context);
    require(bool(source) && succeeded(verify(*source)), "invalid test source");
    auto formula = source->lookupSymbol<func::FuncOp>("formula");
    auto bindings = source->lookupSymbol<func::FuncOp>("bindings");
    llvm::DenseMap<Value, LaneInput> inputs;
    for (unsigned i = 0; i < 3; ++i)
      inputs[formula.getArgument(i)] = {bindings.getArgument(i), i != 1};
    auto admitted = take(admitLaneFormula(formula.front(), inputs,
                                          bindings.getArgument(0).getType(),
                                          nullptr, mathematicalRecipes()));
    require(bool(admitted.formula), "source formula not admitted");
    auto &plan = *admitted.formula;
    cases.run("qualified region and actual upstream CSE " + field, [&] {
      require(succeeded(verify(*plan.region)),
              "upstream verifier refused region");
      auto actual = take(checkFieldRegion(plan));
      require(actual.inputs().size() == 3, "unused input disappeared");
      unsigned multiplies = 0;
      plan.region->walk([&](algebra::FieldMultiplyOp) { ++multiplies; });
      require(multiplies == 1, "upstream CSE did not share scalar work");
    });
    auto mutation = [&](StringRef name, llvm::function_ref<void(ModuleOp)> edit,
                        StringRef code = "field-region-profile") {
      cases.run(name + " " + field, [&] {
        auto retained = std::move(plan.region);
        plan.region =
            OwningOpRef<ModuleOp>(cast<ModuleOp>((*retained)->clone()));
        edit(*plan.region);
        auto result = checkFieldRegion(plan);
        plan.region = std::move(retained);
        refuses(std::move(result), code);
      });
    };
    mutation("shifted input indexing", [&](ModuleOp module) {
      auto op = payload(module);
      auto maps = op.getIndexingMapsArray();
      maps[0] = AffineMap::get(1, 0, getAffineDimExpr(0, &context) + 1);
      op.setIndexingMapsAttr(OpBuilder(&context).getAffineMapArrayAttr(maps));
    });
    mutation("wrong broadcast", [&](ModuleOp module) {
      auto op = payload(module);
      auto maps = op.getIndexingMapsArray();
      maps[1] = AffineMap::getMultiDimIdentityMap(1, &context);
      op.setIndexingMapsAttr(OpBuilder(&context).getAffineMapArrayAttr(maps));
    });
    mutation("reduction iterator", [&](ModuleOp module) {
      auto op = payload(module);
      op.setIteratorTypesAttr(
          OpBuilder(&context).getArrayAttr({linalg::IteratorTypeAttr::get(
              &context, utils::IteratorType::reduction)}));
    });
    mutation("destination contents are not inputs", [&](ModuleOp module) {
      auto &body = payload(module).getRegion().front();
      body.back().setOperand(0, body.getArguments().back());
    });
    mutation("extra library call authority", [&](ModuleOp module) {
      payload(module)->setAttr("library_call",
                               StringAttr::get(&context, "foreign"));
    });
    mutation(
        "actual scalar output changed",
        [&](ModuleOp module) {
          auto &body = payload(module).getRegion().front();
          body.back().setOperand(0, body.getArgument(1));
        },
        "field-region-correspondence");
    mutation(
        "unused malformed field literal",
        [&](ModuleOp module) {
          auto &body = payload(module).getRegion().front();
          OpBuilder builder(&body.back());
          algebra::ConstantFieldOp::create(builder, builder.getUnknownLoc(),
                                           body.getArgument(0).getType(),
                                           "0x2");
        },
        field.starts_with("gf2-") ? "ring-literal" : "field-region-profile");
    mutation("nominal field changed", [&](ModuleOp module) {
      payload(module).getRegion().front().getArgument(0).setType(
          algebra::FieldType::get(&context, "bn254.fr" == field ? "koala-bear"
                                                                : "bn254.fr"));
    });
    cases.run("changed candidate emits no native prefix " + field, [&] {
      auto &body = payload(*plan.region).getRegion().front();
      body.back().setOperand(0, body.getArgument(1));
      unsigned emitted = 0;
      auto vector = bindings.getArgument(0).getType();
      refuses(emitNumericalLanes(plan, vector, bindings.getArgument(3),
                                 LaneResultMode::Map,
                                 [&](const protocol::BindingApplication &,
                                     ValueRange, Type, ArrayRef<std::string>) {
                                   ++emitted;
                                   return Value();
                                 }),
              "field-region-correspondence");
      refuses(emitVectorLanes(
                  plan, vector, bindings.getArgument(3), mathematicalRecipes(),
                  [&](StringRef, ValueRange, Type, ArrayRef<std::string>) {
                    ++emitted;
                    return Value();
                  }),
              "field-region-correspondence");
      require(!emitted, "invalid candidate emitted native operations");
    });
  }
  return cases.result();
}
