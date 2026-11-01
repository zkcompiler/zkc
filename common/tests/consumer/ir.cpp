#include "zkc/Dialect/IR.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Analysis/ResidueArithmetic.h"
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
  context.getOrLoadDialect<zkc::data::DataDialect>();
  auto vector = zkc::data::FieldVectorType::get(&context, "bls12-381.fr");
  auto collection = mlir::cast<zkc::CollectionTypeInterface>(vector);
  if (collection.getCollectionKind() != zkc::CollectionKind::FieldVector ||
      collection.getRank() != 1 || collection.getStaticExtent(0) ||
      !mlir::isa<zkc::algebra::FieldType>(collection.getElementType()))
    return 4;
  // The installed IR reader must link without the lowering/target components.
  auto residue = mlir::parseSourceString<mlir::ModuleOp>(R"(
module {
  func.func @twice(%x: !residue.value<17 : ui8>) -> !residue.value<17 : ui8> {
    %r = "residue.add"(%x, %x) : (!residue.value<17 : ui8>, !residue.value<17 : ui8>) -> !residue.value<17 : ui8>
    return %r : !residue.value<17 : ui8>
  }
})",
                                                         &context);
  auto words = mlir::parseSourceString<mlir::ModuleOp>(R"(
module {
  func.func @twice(%x: i8) -> i8 {
    %wide = arith.extui %x : i8 to i9
    %sum = arith.addi %wide, %wide : i9
    %q = arith.constant 17 : i9
    %reduced = arith.remui %sum, %q : i9
    %r = arith.trunci %reduced : i9 to i8
    return %r : i8
  }
})",
                                                       &context);
  if (!residue || !words || !zkc::residue::consumeArithmetic(*residue, *words))
    return 8;
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
