#include "zkc/Dialect/IR.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
int main() {
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  if (registry.getDialectAllocator("table") ||
      registry.getDialectAllocator("claim"))
    return 1;
  mlir::MLIRContext context(registry);
  auto module = mlir::parseSourceString<mlir::ModuleOp>(R"(
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%x:i1): "protocol.return"(%x) : (i1)->() })
 {sym_name="main",function_type=(i1)->i1,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })",
                                                        &context);
  if (!module || mlir::failed(mlir::verify(*module)))
    return 2;
  module->walk([&](zkc::protocol_ir::MathematicalOp op) {
    op->setAttr("output_roles", mlir::ArrayAttr::get(&context, {}));
  });
  mlir::ScopedDiagnosticHandler expected(
      &context, [](mlir::Diagnostic &) { return mlir::success(); });
  return mlir::succeeded(mlir::verify(*module)) ? 3 : 0;
}
