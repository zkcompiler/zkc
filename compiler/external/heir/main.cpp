#include "lib/Dialect/ModArith/Conversions/ModArithToArith/ModArithToArith.h"
#include "lib/Dialect/ModArith/IR/ModArithDialect.h"
#include "lib/Dialect/Polynomial/Conversions/PolynomialToModArith/PolynomialToModArith.h"
#include "lib/Dialect/Polynomial/IR/PolynomialDialect.h"
#include "lib/Dialect/Polynomial/Transforms/Passes.h"
#include "lib/Dialect/RNS/IR/RNSDialect.h"
#include "lib/Dialect/RNS/Transforms/Passes.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/LLVMIR/LLVMDialect.h"
#include "mlir/Dialect/Linalg/IR/Linalg.h"
#include "mlir/Dialect/MemRef/IR/MemRef.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/Dialect/Tensor/IR/Tensor.h"
#include "mlir/IR/DialectRegistry.h"
#include "mlir/Tools/mlir-opt/MlirOptMain.h"
#include "mlir/Transforms/Passes.h"

int main(int argc, char **argv) {
  mlir::registerTransformsPasses();
  mlir::heir::polynomial::registerPasses();
  mlir::heir::mod_arith::registerPasses();
  mlir::heir::polynomial::registerPolynomialPasses();
  mlir::heir::rns::registerRNSPasses();
  mlir::DialectRegistry registry;
  registry.insert<mlir::heir::mod_arith::ModArithDialect,
                  mlir::heir::polynomial::PolynomialDialect,
                  mlir::heir::rns::RNSDialect, mlir::arith::ArithDialect,
                  mlir::func::FuncDialect, mlir::scf::SCFDialect,
                  mlir::tensor::TensorDialect, mlir::linalg::LinalgDialect,
                  mlir::memref::MemRefDialect, mlir::LLVM::LLVMDialect>();
  return mlir::asMainReturnCode(mlir::MlirOptMain(
      argc, argv, "zkc HEIR arithmetic transformations\n", registry));
}
