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
  check<zkc::local::LocalDialect>(native, "local");
  check<zkc::plan::PlanDialect>(native, "plan");

  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  require(!zkc::hasProtocolDialects(context));
  context.getOrLoadDialect<zkc::protocol_ir::ProtocolDialect>();
  require(!zkc::hasProtocolDialects(context));
  context.loadAllAvailableDialects();
  require(zkc::hasProtocolDialects(context));
  check<zkc::protocol_ir::ProtocolDialect>(context, "protocol");
  check<zkc::local::LocalDialect>(context, "local");
  check<zkc::crypto::CryptoDialect>(context, "crypto");
  require(!registry.getDialectAllocator("table"));
  check<zkc::algebra::AlgebraDialect>(context, "algebra");
  check<zkc::poly::PolynomialDialect>(context, "poly");
  check<zkc::plan::PlanDialect>(context, "plan");
  check<zkc::pcs::PCSDialect>(context, "pcs");
  check<zkc::oracle::OracleDialect>(context, "oracle");
  check<zkc::relation::RelationDialect>(context, "relation");
  require(!registry.getDialectAllocator("claim"));
  check<mlir::func::FuncDialect>(context, "func");
}
