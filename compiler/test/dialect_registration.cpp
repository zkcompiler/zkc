#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/DialectRegistry.h"
#include "zkc/Dialect/IR.h"
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
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  require(!zkc::hasProtocolDialects(context));
  context.getOrLoadDialect<zkc::PIRDialect>();
  require(!zkc::hasProtocolDialects(context));
  context.loadAllAvailableDialects();
  require(zkc::hasProtocolDialects(context));
  check<zkc::PIRDialect>(context, "pir");
  check<zkc::AlgebraDialect>(context, "algebra");
  check<zkc::PolynomialDialect>(context, "poly");
  check<zkc::PlanDialect>(context, "plan");
  check<zkc::PCSDialect>(context, "pcs");
  check<zkc::OracleDialect>(context, "oracle");
  check<zkc::RelationDialect>(context, "relation");
  check<zkc::ClaimDialect>(context, "claim");
  check<mlir::func::FuncDialect>(context, "func");
}
