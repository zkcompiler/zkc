#include "Admission.h"
#include "lib/Dialect/ModArith/IR/ModArithDialect.h"
#include "lib/Dialect/Polynomial/IR/PolynomialDialect.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/Tensor/IR/Tensor.h"
#include "mlir/IR/DialectRegistry.h"
#include "mlir/Parser/Parser.h"
#include "llvm/Support/raw_ostream.h"

int main(int argc, char **argv) {
  if (argc != 2) {
    llvm::errs() << "usage: zkc-heir-place SOURCE.mlir\n";
    return 2;
  }
  mlir::DialectRegistry registry;
  registry.insert<mlir::heir::mod_arith::ModArithDialect,
                  mlir::heir::polynomial::PolynomialDialect,
                  mlir::arith::ArithDialect, mlir::func::FuncDialect,
                  mlir::tensor::TensorDialect>();
  mlir::MLIRContext context(registry);
  auto source = mlir::parseSourceFile<mlir::ModuleOp>(argv[1], &context);
  if (!source)
    return 1;
  auto candidate = zkc::heir::placeTransforms(*source);
  if (mlir::failed(candidate))
    return 1;
  (*candidate)->print(llvm::outs());
  llvm::outs() << '\n';
  return 0;
}
