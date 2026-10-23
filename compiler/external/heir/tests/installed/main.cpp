#include "lib/Dialect/ModArith/IR/ModArithDialect.h"
#include "lib/Dialect/ModArith/IR/ModArithOps.h"
#include "lib/Dialect/Polynomial/IR/PolynomialDialect.h"
#include "lib/Dialect/Polynomial/IR/PolynomialOps.h"
#include "lib/Dialect/RNS/IR/RNSOps.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Parser/Parser.h"
#include "zkc/heir/Admission.h"
int main() {
  mlir::DialectRegistry dialects;
  dialects.insert<mlir::heir::polynomial::PolynomialDialect,
                  mlir::heir::mod_arith::ModArithDialect,
                  mlir::func::FuncDialect>();
  mlir::MLIRContext context(dialects);
  auto module = mlir::parseSourceString<mlir::ModuleOp>(R"(
!c = !mod_arith.int<17:i32>
#r = #polynomial.ring<coefficientType=!c, polynomialModulus=<1+x**4>>
!p = !polynomial.polynomial<ring=#r>
module { func.func @compute(%x:tensor<4xi32>)->tensor<4xi32> {
%m=mod_arith.encapsulate %x : tensor<4xi32> -> tensor<4x!c>
%p=polynomial.from_tensor %m : tensor<4x!c> -> !p
%v=polynomial.mul %p,%p : !p
%t=polynomial.to_tensor %v : !p -> tensor<4x!c>
%r=mod_arith.lift standard %t : tensor<4x!c> -> tensor<4xi32>
return %r : tensor<4xi32>
} })",
                                                        &context);
  if (!module)
    return 1;
  using namespace zkc::heir;
  auto result = placeTransforms(*module);
  if (mlir::failed(result))
    return 2;
  uint64_t inspection = 1000000;
  if (mlir::failed(readArithmetic(*module, inspection)))
    return 6;
  uint64_t rootLimited = 1000000 - inspection + 127;
  PlacementStatus status;
  auto noRoot = placeTransforms(*module, &status, &rootLimited);
  if (mlir::succeeded(noRoot) || status != PlacementStatus::Unavailable)
    return 7;
  const Expression left{{{0}, 1}}, right{{{1}, 1}}, malformed{{{0}, 17}};
  bool exhausted = false;
  uint64_t allowance = 8;
  auto exact =
      combine(ArithmeticOperation::Add, left, right, 17, allowance, &exhausted);
  if (mlir::failed(exact) || allowance != 0 || exhausted)
    return 3;
  allowance = 7;
  auto limited =
      combine(ArithmeticOperation::Add, left, right, 17, allowance, &exhausted);
  if (mlir::succeeded(limited) || allowance != 0 || !exhausted)
    return 4;
  allowance = 2;
  auto invalid = combine(ArithmeticOperation::Add, malformed, right, 17,
                         allowance, &exhausted);
  if (mlir::succeeded(invalid) || allowance != 0 || exhausted)
    return 5;
  return 0;
}
