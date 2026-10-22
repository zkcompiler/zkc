#include "Admission.h"
#include "lib/Dialect/ModArith/IR/ModArithDialect.h"
#include "lib/Dialect/Polynomial/IR/PolynomialDialect.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/DialectRegistry.h"
#include "mlir/Parser/Parser.h"
#include "llvm/Support/raw_ostream.h"

int main(int argc, char **argv) {
  if (argc != 3) {
    llvm::errs() << "usage: zkc-heir-check SOURCE.mlir CANDIDATE.mlir\n";
    return 2;
  }
  mlir::DialectRegistry registry;
  registry.insert<mlir::heir::mod_arith::ModArithDialect,
                  mlir::heir::polynomial::PolynomialDialect,
                  mlir::arith::ArithDialect, mlir::func::FuncDialect>();
  mlir::MLIRContext context(registry);
  auto source = mlir::parseSourceFile<mlir::ModuleOp>(argv[1], &context);
  auto candidate = mlir::parseSourceFile<mlir::ModuleOp>(argv[2], &context);
  if (!source || !candidate ||
      mlir::failed(zkc::heir::compareArithmetic(*source, *candidate)))
    return 1;
  return 0;
}
