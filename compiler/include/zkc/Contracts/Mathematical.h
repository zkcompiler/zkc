#ifndef ZKC_CONTRACTS_MATHEMATICAL_H
#define ZKC_CONTRACTS_MATHEMATICAL_H
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"

namespace zkc {
/// Logical identities shared by source checking and admitted IR interfaces.
/// This vocabulary does not select an operation implementation or a backend.
enum class MathematicalIdentity {
  FieldAdd,
  FieldMultiply,
  FieldEqual,
  GroupAdd,
  GroupScale,
  GroupEqual,
  Pairing,
  BooleanConstant,
  BooleanAnd,
  BooleanOr,
  BooleanXor,
  BooleanEqual,
  BooleanNotEqual,
  Select,
  FieldConstant,
  FieldSubtract,
  ArrayFromElements,
  ArrayAt,
  PolynomialConstant,
  PolynomialFromCoefficients,
  PolynomialMLE,
  PolynomialAdd,
  PolynomialMultiply,
  PolynomialFix,
  PolynomialSum,
  PolynomialEvaluate,
  PolynomialCoefficients,
  PolynomialEvaluateDomain,
  PolynomialInterpolate,
  PolynomialFixTable
};
/// Library authoring hooks for total mathematics. Static roots are a field
/// followed by the indicated number of naturals. Domain points are canonical
/// field literals, independently checked by native mathematical admission.
struct MathematicalIntrinsic {
  llvm::StringRef name;
  MathematicalIdentity identity;
  unsigned naturals;
  bool domainPoints = false;
};
llvm::ArrayRef<MathematicalIntrinsic> mathematicalIntrinsics();
const MathematicalIntrinsic *mathematicalIntrinsic(llvm::StringRef);
} // namespace zkc

#endif
