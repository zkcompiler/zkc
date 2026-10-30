#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Matchers.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Transforms/FoldUtils.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include <limits>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
int main() {
  DialectRegistry registry;
  registry.insert<data::DataDialect, func::FuncDialect>();
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  ScopedDiagnosticHandler quiet(&context,
                                [](Diagnostic &) { return success(); });
  auto *dialect = context.getLoadedDialect<data::DataDialect>();
  OpBuilder builder(&context);
  auto type = builder.getIntegerType(64, false);
  Cases cases;
  cases.run("standard folder preserves exact unsigned values and type", [&] {
    auto module = parseSourceString<ModuleOp>(
        "module { func.func @constants() { return } }", &context);
    require(bool(module), "constant scope");
    auto function = *module->getOps<func::FuncOp>().begin();
    OperationFolder folder(&context);
    for (uint64_t number : {uint64_t(0), uint64_t(1), uint64_t(1) << 63,
                            std::numeric_limits<uint64_t>::max()}) {
      auto attribute = builder.getIntegerAttr(type, number);
      auto value = folder.getOrCreateConstant(&function.front(), dialect,
                                              attribute, type);
      Attribute folded;
      require(value && value.getType() == type &&
                  value.getDefiningOp<data::IndexOp>() &&
                  matchPattern(value, m_Constant(&folded)) &&
                  folded == attribute,
              "standard constant folding changed width or value");
      require(folder.getOrCreateConstant(&function.front(), dialect, attribute,
                                         type) == value,
              "standard folder cannot share a pure constant");
    }
    require(succeeded(verify(*module)),
            "materialized constants failed formation");
  });
  cases.run(
      "materialization refuses incompatible attribute and result kinds", [&] {
        auto module = ModuleOp::create(builder.getUnknownLoc());
        builder.setInsertionPointToEnd(module.getBody());
        for (auto wrong :
             {builder.getI64Type(), builder.getIntegerType(64, true),
              builder.getIntegerType(32, false)})
          require(!dialect->materializeConstant(
                      builder, builder.getIntegerAttr(wrong, 1), type,
                      module.getLoc()) &&
                      !dialect->materializeConstant(
                          builder, builder.getIntegerAttr(type, 1), wrong,
                          module.getLoc()),
                  "materializer coerced a constant type");
        require(!dialect->materializeConstant(
                    builder, builder.getStringAttr("1"), type, module.getLoc()),
                "materializer accepted a legacy spelling");
        module.erase();
      });
  cases.run("native formation rejects strings and non-ui64 literals", [&] {
    for (StringRef value : {"\"1\"", "1 : i64", "1 : si64", "1 : ui32",
                            "18446744073709551616 : ui64"}) {
      auto source = "module { func.func @bad() -> ui64 { %v = \"data.index\"() "
                    "{value=" +
                    value.str() + "} : () -> ui64 func.return %v : ui64 } }";
      require(!parseSourceString<ModuleOp>(source, &context),
              "malformed pure index constant accepted");
    }
  });
  return cases.result();
}
