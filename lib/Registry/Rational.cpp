//===- Rational.cpp - exact rational arithmetic -----------------*- C++ -*-===//
#include "zkc/Registry/Rational.h"

#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallString.h"

using namespace llvm;

namespace zkc {
namespace registry {

// APInt is fixed-width; these helpers resize BOTH operands to one
// width large enough that magnitude arithmetic can never wrap.
// zextOrTrunc to any width >= the active bits preserves the value.
static APInt widen(const APInt &value, unsigned width) {
  return value.zextOrTrunc(std::max(width, value.getActiveBits()));
}

static APInt mulWide(const APInt &a, const APInt &b) {
  unsigned width =
      std::max(a.getActiveBits() + b.getActiveBits() + 1, 1u);
  return widen(a, width) * widen(b, width);
}

static APInt addWide(const APInt &a, const APInt &b) {
  unsigned width = std::max(a.getActiveBits(), b.getActiveBits()) + 2;
  return widen(a, width) + widen(b, width);
}

/// a - b for magnitudes with a >= b.
static APInt subWide(const APInt &a, const APInt &b) {
  unsigned width = std::max(a.getBitWidth(), b.getBitWidth());
  return widen(a, width) - widen(b, width);
}

static int compareMagnitude(const APInt &a, const APInt &b) {
  unsigned width = std::max(a.getBitWidth(), b.getBitWidth());
  APInt wa = widen(a, width), wb = widen(b, width);
  if (wa.ult(wb))
    return -1;
  return wa == wb ? 0 : 1;
}

void Rational::canonicalize() {
  if (num.isZero()) {
    negative = false;
    num = APInt(1, 0);
    den = APInt(1, 1);
    return;
  }
  unsigned width = std::max(num.getBitWidth(), den.getBitWidth());
  APInt g = APIntOps::GreatestCommonDivisor(widen(num, width),
                                            widen(den, width));
  num = widen(num, width).udiv(g);
  den = widen(den, width).udiv(g);
  // Trim storage back to the active bits.
  unsigned trim = std::max({num.getActiveBits(), den.getActiveBits(), 1u});
  num = num.zextOrTrunc(trim);
  den = den.zextOrTrunc(trim);
}

llvm::Expected<Rational> Rational::fromDecimal(llvm::StringRef text) {
  bool neg = text.consume_front("-");
  if (text.empty() ||
      !llvm::all_of(text, [](char c) { return c >= '0' && c <= '9'; }))
    return llvm::createStringError("not a decimal integer: '" + text + "'");
  if (text.size() > 1 && text.front() == '0')
    return llvm::createStringError("decimal integers carry no leading "
                                   "zeros: '" +
                                   text + "'");
  // 10 bits per 3 digits overestimates safely.
  unsigned width = static_cast<unsigned>(text.size()) * 4 + 4;
  APInt value(width, 0);
  APInt ten(width, 10);
  for (char c : text) {
    value = value * ten + APInt(width, static_cast<uint64_t>(c - '0'));
  }
  Rational result;
  result.negative = neg;
  result.num = value;
  result.den = APInt(1, 1);
  result.canonicalize();
  return result;
}

llvm::Expected<Rational> Rational::fromDecimalPair(llvm::StringRef numText,
                                                   llvm::StringRef denText) {
  auto n = fromDecimal(numText);
  if (!n)
    return n.takeError();
  auto d = fromDecimal(denText);
  if (!d)
    return d.takeError();
  if (d->isZero())
    return llvm::createStringError("rational denominator is zero");
  return n->div(*d);
}

Rational Rational::fromInteger(int64_t value) {
  Rational result;
  result.negative = value < 0;
  uint64_t magnitude =
      value < 0 ? (~static_cast<uint64_t>(value)) + 1 : value;
  result.num = APInt(64, magnitude);
  result.den = APInt(1, 1);
  result.canonicalize();
  return result;
}

Rational Rational::add(const Rational &o) const {
  // a/b + c/d = (ad + cb) / bd, with sign handling on magnitudes.
  APInt ad = mulWide(num, o.den);
  APInt cb = mulWide(o.num, den);
  Rational result;
  result.den = mulWide(den, o.den);
  if (negative == o.negative) {
    result.num = addWide(ad, cb);
    result.negative = negative;
  } else if (compareMagnitude(ad, cb) >= 0) {
    result.num = subWide(ad, cb);
    result.negative = negative;
  } else {
    result.num = subWide(cb, ad);
    result.negative = o.negative;
  }
  result.canonicalize();
  return result;
}

Rational Rational::sub(const Rational &o) const {
  Rational flipped = o;
  if (!flipped.isZero())
    flipped.negative = !flipped.negative;
  return add(flipped);
}

Rational Rational::mul(const Rational &o) const {
  Rational result;
  result.negative = negative != o.negative;
  result.num = mulWide(num, o.num);
  result.den = mulWide(den, o.den);
  result.canonicalize();
  return result;
}

llvm::Expected<Rational> Rational::div(const Rational &o) const {
  if (o.isZero())
    return llvm::createStringError("division by zero in loss arithmetic");
  Rational result;
  result.negative = negative != o.negative;
  result.num = mulWide(num, o.den);
  result.den = mulWide(den, o.num);
  result.canonicalize();
  return result;
}

llvm::Expected<Rational> Rational::pow(int64_t exponent) const {
  if (exponent < 0 && isZero())
    return llvm::createStringError("zero to a negative power");
  Rational base = *this;
  if (exponent < 0) {
    Rational one = fromInteger(1);
    auto inverted = one.div(base);
    if (!inverted)
      return inverted.takeError();
    base = *inverted;
    exponent = -exponent;
  }
  Rational result = fromInteger(1);
  while (exponent > 0) {
    if (exponent & 1)
      result = result.mul(base);
    base = base.mul(base);
    exponent >>= 1;
  }
  return result;
}

int Rational::compare(const Rational &o) const {
  if (negative != o.negative)
    return negative ? -1 : 1;
  int magnitude = compareMagnitude(mulWide(num, o.den), mulWide(o.num, den));
  return negative ? -magnitude : magnitude;
}

llvm::Expected<int64_t> Rational::ceilLog2() const {
  if (isZero() || negative)
    return llvm::createStringError(
        "log2 of a non-positive loss has no meaning");
  // ceil(log2(num/den)) is the smallest k with num <= den * 2^k.
  // Bracket via bit widths, then settle exactly.
  int64_t k = static_cast<int64_t>(num.getActiveBits()) -
              static_cast<int64_t>(den.getActiveBits());
  auto holds = [&](int64_t candidate) {
    // num <= den * 2^candidate  (shift whichever side keeps
    // magnitudes non-negative).
    if (candidate >= 0) {
      APInt shifted = widen(den, den.getActiveBits() +
                                     static_cast<unsigned>(candidate) + 1)
                          .shl(static_cast<unsigned>(candidate));
      return compareMagnitude(num, shifted) <= 0;
    }
    APInt shifted = widen(num, num.getActiveBits() +
                                   static_cast<unsigned>(-candidate) + 1)
                        .shl(static_cast<unsigned>(-candidate));
    return compareMagnitude(shifted, den) <= 0;
  };
  while (!holds(k))
    ++k;
  while (k > INT64_MIN + 1 && holds(k - 1))
    --k;
  return k;
}

// The integer floor/ceil magnitudes of |num|/den, shared by
// floorToInt/ceilToInt; den >= 1, so udiv/urem are exact.
static llvm::Expected<int64_t> toInt(const APInt &num, const APInt &den,
                                     bool negative, bool wantFloor) {
  unsigned width = std::max(num.getActiveBits(), den.getActiveBits()) + 2;
  APInt n = widen(num, width), d = widen(den, width);
  APInt q = n.udiv(d);          // floor(|num|/den)
  APInt roundUp = q + APInt(width, 1);
  bool exact = n.urem(d).isZero();
  // floor(±x): + -> floor(|x|) = q; - -> -ceil(|x|).
  // ceil(±x):  + -> ceil(|x|);      - -> -floor(|x|) = -q.
  APInt mag = wantFloor ? (negative ? (exact ? q : roundUp) : q)
                        : (negative ? q : (exact ? q : roundUp));
  if (mag.getActiveBits() > 63)
    return llvm::createStringError("dyadic exponent overflows int64");
  int64_t m = static_cast<int64_t>(mag.getZExtValue());
  return negative ? -m : m;
}

llvm::Expected<int64_t> Rational::floorToInt() const {
  return toInt(num, den, negative, /*wantFloor=*/true);
}

llvm::Expected<int64_t> Rational::ceilToInt() const {
  return toInt(num, den, negative, /*wantFloor=*/false);
}

std::string Rational::str() const {
  std::string text = numStr();
  if (!(den.getActiveBits() <= 1 && den == 1))
    text += "/" + denStr();
  return text;
}

std::string Rational::numStr() const {
  llvm::SmallString<40> digits;
  num.toString(digits, 10, /*isSigned=*/false);
  return (negative ? "-" : "") + std::string(digits);
}

std::string Rational::denStr() const {
  llvm::SmallString<40> digits;
  den.toString(digits, 10, /*isSigned=*/false);
  return std::string(digits);
}

} // namespace registry
} // namespace zkc
