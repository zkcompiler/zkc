#ifndef ZKC_CONTRACTS_MATHEMATICAL_H
#define ZKC_CONTRACTS_MATHEMATICAL_H

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
} // namespace zkc

#endif
