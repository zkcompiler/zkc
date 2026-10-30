#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/DialectRegistry.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Interfaces/Mathematical.h"
#include <cstdlib>

namespace {
void require(bool condition) {
  if (!condition)
    std::abort();
}
template <typename Dialect>
void check(mlir::MLIRContext &context, llvm::StringRef name) {
  // Independent expectations catch a descriptor/ODS namespace disagreement.
  require(Dialect::getDialectNamespace() == name);
  require(context.getLoadedDialect<Dialect>() ==
          context.getLoadedDialect(name));
  require(context.getLoadedDialect<Dialect>() != nullptr);
}
} // namespace

int main() {
  // Loading Polynomial alone must initialize storage used by its verifiers,
  // even when neither dependency has appeared in parsed input.
  mlir::MLIRContext minimal;
  minimal.getOrLoadDialect<zkc::poly::PolynomialDialect>();
  check<zkc::algebra::AlgebraDialect>(minimal, "algebra");
  check<zkc::data::DataDialect>(minimal, "data");
  require(!minimal.getLoadedDialect("runtime"));
  require(!minimal.getLoadedDialect("exec"));

  mlir::DialectRegistry nativeRegistry;
  zkc::registerDialects(nativeRegistry);
  require(!nativeRegistry.getDialectAllocator("table"));
  mlir::MLIRContext native(nativeRegistry);
  native.loadAllAvailableDialects();
  require(zkc::hasProtocolDialects(native));
  require(mlir::OperationName("arith.andi", &native)
              .hasInterface<zkc::MathematicalOpInterface>());
  require(!native.getLoadedDialect("table"));
  require(!native.isOperationRegistered("protocol.exec_func"));
  check<zkc::protocol_ir::ProtocolDialect>(native, "protocol");
  for (auto name : {"local", "kernel", "plan"}) {
    require(!nativeRegistry.getDialectAllocator(name));
    require(!native.getLoadedDialect(name));
  }
  for (auto name :
       {"local.func", "local.apply", "kernel.call", "algebra.map_realize"})
    require(!native.isOperationRegistered(name));
  require(!nativeRegistry.getDialectAllocator("plan"));
  require(!native.getLoadedDialect("plan"));
  for (auto name : {"plan.apply", "plan.bool_constant", "plan.release"})
    require(!native.isOperationRegistered(name));
  check<zkc::runtime::RuntimeDialect>(native, "runtime");
  require(native.isOperationRegistered("runtime.binding"));
  require(!native.isOperationRegistered("local.binding"));

  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  require(!zkc::hasProtocolDialects(context));
  context.getOrLoadDialect<zkc::protocol_ir::ProtocolDialect>();
  require(!zkc::hasProtocolDialects(context));
  context.loadAllAvailableDialects();
  require(zkc::hasProtocolDialects(context));
  check<zkc::protocol_ir::ProtocolDialect>(context, "protocol");
  require(!context.getLoadedDialect("local"));
  check<zkc::crypto::CryptoDialect>(context, "crypto");
  require(!registry.getDialectAllocator("table"));
  check<zkc::algebra::AlgebraDialect>(context, "algebra");
  check<zkc::poly::PolynomialDialect>(context, "poly");
  require(!registry.getDialectAllocator("plan"));
  check<zkc::commitment::CommitmentDialect>(context, "commitment");
  require(!registry.getDialectAllocator("pcs"));
  require(!registry.getDialectAllocator("oracle"));
  check<zkc::relation::RelationDialect>(context, "relation");
  require(!registry.getDialectAllocator("claim"));
  check<mlir::func::FuncDialect>(context, "func");
}
