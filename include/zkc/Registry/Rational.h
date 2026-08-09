//===- Rational.h - exact rational arithmetic -------------------*- C++ -*-===//
// The exact number type of the Soundness Kernel (docs/spec/soundness.md):
// bound arithmetic is exact — every stored and recomputed value is a
// canonical rational over arbitrary-precision integers, and no
// rounding occurs anywhere inside bound-expression evaluation or
// comparison.
//===----------------------------------------------------------------------===//
#ifndef ZKC_REGISTRY_RATIONAL_H
#define ZKC_REGISTRY_RATIONAL_H

#include "llvm/ADT/APInt.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"

#include <string>

namespace zkc {
namespace registry {

/// An exact rational in canonical form: magnitude numerator and
/// denominator with gcd 1, denominator >= 1, no negative zero.
/// Widths grow as needed; nothing here saturates or wraps.
class Rational {
public:
  /// Zero.
  Rational() : num(1, 0), den(1, 1) {}

  /// Parse a decimal integer string (optional leading '-'; digits
  /// only — the registry spelling; no leading zeros beyond "0").
  static llvm::Expected<Rational> fromDecimal(llvm::StringRef text);

  /// num / den from two decimal strings (den must be nonzero).
  static llvm::Expected<Rational> fromDecimalPair(llvm::StringRef num,
                                                  llvm::StringRef den);

  static Rational fromInteger(int64_t value);

  Rational add(const Rational &o) const;
  Rational sub(const Rational &o) const;
  Rational mul(const Rational &o) const;
  llvm::Expected<Rational> div(const Rational &o) const;
  /// Integer power; exponent may be negative iff the base is nonzero.
  llvm::Expected<Rational> pow(int64_t exponent) const;

  /// Total order: negative iff *this < o, zero iff equal.
  int compare(const Rational &o) const;

  bool isZero() const { return num.isZero(); }
  bool isNegative() const { return negative; }

  /// ceil(log2(x)) for x > 0 — the presentation-boundary rounding
  /// for a loss (ε rounds UP). Errors on x <= 0.
  llvm::Expected<int64_t> ceilLog2() const;

  /// The greatest integer <= this value (floor) and least integer >=
  /// this value (ceil), for the directed dyadic bound of a half-integer
  /// power (2^x bounded by 2^floor(x) below / 2^ceil(x) above). Errors
  /// if the result overflows int64.
  llvm::Expected<int64_t> floorToInt() const;
  llvm::Expected<int64_t> ceilToInt() const;

  /// "num/den" (or just "num" when den == 1), decimal.
  std::string str() const;
  std::string numStr() const;
  std::string denStr() const;

private:
  bool negative = false;
  llvm::APInt num; // magnitude
  llvm::APInt den; // magnitude, >= 1

  void canonicalize();
};

} // namespace registry
} // namespace zkc

#endif // ZKC_REGISTRY_RATIONAL_H
