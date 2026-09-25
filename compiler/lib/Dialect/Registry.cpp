#include "zkc/Dialect/Registry.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Dialect/Algebra/IR/AlgebraDialect.h"
#include "zkc/Dialect/Claim/IR/ClaimDialect.h"
#include "zkc/Dialect/Oracle/IR/OracleDialect.h"
#include "zkc/Dialect/PCS/IR/PCSDialect.h"
#include "zkc/Dialect/PIR/IR/PIRDialect.h"
#include "zkc/Dialect/Plan/IR/PlanDialect.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialDialect.h"
#include "zkc/Dialect/Relation/IR/RelationDialect.h"

namespace zkc {
void registerDialects(mlir::DialectRegistry &registry) {
  registry.insert<PIRDialect, AlgebraDialect, PolynomialDialect, PlanDialect,
                  PCSDialect, OracleDialect, RelationDialect, ClaimDialect,
                  mlir::func::FuncDialect>();
}
} // namespace zkc
