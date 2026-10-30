#include "zkc/Dialect/IR.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Analysis/StructuredComputation.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Interfaces/Collection.h"
int main() {
  if (zkc::mathematical::readStructuredComputation({}))
    return 6;
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  if (registry.getDialectAllocator("table") ||
      registry.getDialectAllocator("claim") ||
      registry.getDialectAllocator("entry") ||
      !registry.getDialectAllocator("exec"))
    return 1;
  mlir::MLIRContext context(registry);
  context.getOrLoadDialect<zkc::exec::ExecDialect>();
  auto outcome = zkc::exec::OutcomeType::get(&context, {});
  if (!outcome.getPayload().empty())
    return 5;
  context.getOrLoadDialect<zkc::algebra::AlgebraDialect>();
  auto vector = zkc::algebra::FieldVectorType::get(&context, "bls12-381.fr");
  auto collection = mlir::cast<zkc::CollectionTypeInterface>(vector);
  if (collection.getCollectionKind() != zkc::CollectionKind::FieldVector ||
      collection.getRank() != 1 || collection.getStaticExtent(0))
    return 4;
  auto module = mlir::parseSourceString<mlir::ModuleOp>(R"(
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%x:i1): "protocol.return"(%x) : (i1)->() })
 {sym_name="main",function_type=(i1)->i1,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })",
                                                        &context);
  if (!module || mlir::failed(zkc::admitStage(*module)))
    return 2;
  module->walk([&](zkc::protocol_ir::MathematicalOp op) {
    op->setAttr("output_roles", mlir::ArrayAttr::get(&context, {}));
  });
  mlir::ScopedDiagnosticHandler expected(
      &context, [](mlir::Diagnostic &) { return mlir::success(); });
  if (mlir::failed(mlir::verify(*module)))
    return 7;
  return mlir::succeeded(zkc::admitStage(*module)) ? 3 : 0;
}
