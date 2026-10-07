#include "zkc/Contracts/Mathematical.h"
#include "llvm/ADT/STLExtras.h"
namespace zkc {
llvm::ArrayRef<MathematicalIntrinsic> mathematicalIntrinsics() {
  using I = MathematicalIdentity;
  static const MathematicalIntrinsic values[] = {
      {"array.pack", I::ArrayFromElements, 1},
      {"array.at", I::ArrayAt, 2},
      {"poly.constant", I::PolynomialConstant, 1},
      {"poly.from_coefficients", I::PolynomialFromCoefficients, 1},
      {"poly.mle", I::PolynomialMLE, 1},
      {"poly.add", I::PolynomialAdd, 1},
      {"poly.multiply", I::PolynomialMultiply, 1},
      {"poly.fix", I::PolynomialFix, 2},
      {"poly.sum_suffix", I::PolynomialSum, 2},
      {"poly.evaluate", I::PolynomialEvaluate, 1},
      {"poly.coefficients", I::PolynomialCoefficients, 1},
      {"poly.evaluate_domain", I::PolynomialEvaluateDomain, 0, true},
      {"poly.interpolate", I::PolynomialInterpolate, 0, true},
      {"poly.fix_table", I::PolynomialFixTable, 2},
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
