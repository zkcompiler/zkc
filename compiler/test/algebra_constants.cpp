#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/Tensor/IR/Tensor.h"
#include "mlir/IR/Matchers.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Transforms/FoldUtils.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Algebra/Parameters.h"
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
int main() {
  DialectRegistry registry;
  registry.insert<algebra::AlgebraDialect, func::FuncDialect,
                  tensor::TensorDialect>();
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  ScopedDiagnosticHandler quiet(&context,
                                [](Diagnostic &) { return success(); });
  auto *dialect = context.getLoadedDialect<algebra::AlgebraDialect>();
  OpBuilder builder(&context);
  Cases cases;
  for (StringRef domain : {"koala-bear", "bls12-381.fr",
                           "gf2-64.pentanomial-4-3-1.ext3-trinomial1"})
    cases.run("constant folding preserves " + domain, [&] {
      auto module = parseSourceString<ModuleOp>(
          "module { func.func @constants() { return } }", &context);
      auto function = *module->getOps<func::FuncOp>().begin();
      auto type = algebra::FieldType::get(&context, domain);
      OperationFolder folder(&context);
      llvm::SmallVector<llvm::APInt> values{
          llvm::APInt(64, 0), llvm::APInt(64, 1), llvm::APInt(64, 17)};
      if (domain.contains("ext3"))
        values.push_back(llvm::APInt::getAllOnes(192));
      for (const auto &number : values) {
        auto literal = take(algebra::makeFieldLiteral(type, number));
        require(cast<TypedAttr>(literal).getType() == type,
                "typed literal changed the nominal field");
        auto value = folder.getOrCreateConstant(&function.front(), dialect,
                                                literal, type);
        Attribute folded;
        require(value && value.getType() == type &&
                    value.getDefiningOp<algebra::ConstantFieldOp>() &&
                    matchPattern(value, m_Constant(&folded)) &&
                    folded == literal,
                "standard folder changed the field value");
        require(folder.getOrCreateConstant(&function.front(), dialect, literal,
                                           type) == value,
                "standard folder did not share a pure field constant");
      }
      require(succeeded(verify(*module)),
              "materialized field constants failed formation");
    });
  cases.run("upstream tensor folding preserves opaque field elements", [&] {
    auto module = parseSourceString<ModuleOp>(R"mlir(
!F = !algebra.field<"koala-bear">
module { func.func @field_tensor()->tensor<1x!F> {
  %v = "algebra.constant"() {value=#algebra.literal<!F, 17 : ui31>} : ()->!F
  %t = tensor.from_elements %v : tensor<1x!F>
  return %t : tensor<1x!F>
} })mlir",
                                              &context);
    require(bool(module), "typed field tensor did not parse");
    auto function = *module->getOps<func::FuncOp>().begin();
    auto packed = *function.front().getOps<tensor::FromElementsOp>().begin();
    OperationFolder folder(&context);
    require(failed(folder.tryToFold(packed)),
            "unexpected builtin dense field constant");
    require(succeeded(verify(*module)),
            "tensor folding damaged the nominal field");
  });
  cases.run("materialization refuses field substitution and malformed carriers",
            [&] {
              auto module = ModuleOp::create(builder.getUnknownLoc());
              builder.setInsertionPointToEnd(module.getBody());
              auto field = algebra::FieldType::get(&context, "koala-bear");
              auto other = algebra::FieldType::get(&context, "baby-bear");
              auto literal =
                  take(algebra::makeFieldLiteral(field, llvm::APInt(1, 1)));
              require(!dialect->materializeConstant(builder, literal, other,
                                                    module.getLoc()),
                      "materializer changed the field");
              auto malformed = algebra::FieldLiteralAttr::get(
                  &context, field, builder.getI64IntegerAttr(1));
              require(!dialect->materializeConstant(builder, malformed, field,
                                                    module.getLoc()),
                      "materializer accepted a signed carrier");
              require(!dialect->materializeConstant(builder,
                                                    builder.getStringAttr("1"),
                                                    field, module.getLoc()),
                      "materializer accepted a string fallback");
              auto overflow =
                  algebra::makeFieldLiteral(field, llvm::APInt(64, 2130706433));
              require(!overflow,
                      "native literal construction reduced modulo the field");
              llvm::consumeError(overflow.takeError());
              module.erase();
            });
  cases.run("assembly rejects malformed value carriers", [&] {
    for (StringRef value : {"\"1\"", "#algebra.literal<!F, 1 : i31>",
                            "#algebra.literal<!F, 1 : ui32>",
                            "#algebra.literal<!F, 2130706433 : ui31>"}) {
      auto source = "!F = !algebra.field<\"koala-bear\">\nmodule {func.func "
                    "@bad()->!F {%v=\"algebra.constant\"() {value=" +
                    value.str() + "} : ()->!F return %v : !F}}";
      require(!parseSourceString<ModuleOp>(source, &context),
              "malformed field constant accepted");
    }
  });
  return cases.result();
}
