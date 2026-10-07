#include "zkc/Contracts/Mathematical.h"
#include "llvm/ADT/STLExtras.h"
namespace zkc {
llvm::ArrayRef<MathematicalIntrinsic> mathematicalIntrinsics() {
  using I = MathematicalIdentity;
  using D = MathematicalIntrinsic::Domain;
  static const MathematicalIntrinsic values[] = {
      {"bool.and", I::BooleanAnd, D::Boolean},
      {"bool.or", I::BooleanOr, D::Boolean},
      {"bool.xor", I::BooleanXor, D::Boolean},
      {"array.pack", I::ArrayFromElements, D::Field, 1},
      {"array.at", I::ArrayAt, D::Field, 2},
      {"poly.constant", I::PolynomialConstant, D::Field, 1},
      {"poly.from_coefficients", I::PolynomialFromCoefficients, D::Field, 1},
      {"poly.mle", I::PolynomialMLE, D::Field, 1},
      {"poly.add", I::PolynomialAdd, D::Field, 1},
      {"poly.multiply", I::PolynomialMultiply, D::Field, 1},
      {"poly.fix", I::PolynomialFix, D::Field, 2},
      {"poly.sum_suffix", I::PolynomialSum, D::Field, 2},
      {"poly.evaluate", I::PolynomialEvaluate, D::Field, 1},
      {"poly.coefficients", I::PolynomialCoefficients, D::Field, 1},
      {"poly.evaluate_domain", I::PolynomialEvaluateDomain, D::Field, 0, true},
      {"poly.interpolate", I::PolynomialInterpolate, D::Field, 0, true},
      {"poly.fix_table", I::PolynomialFixTable, D::Field, 2},
  };
  return values;
}
const MathematicalIntrinsic *mathematicalIntrinsic(llvm::StringRef name) {
  auto values = mathematicalIntrinsics();
  auto found = llvm::find_if(
      values, [&](const auto &value) { return value.name == name; });
  return found == values.end() ? nullptr : &*found;
}
} // namespace zkc
