//===- RationalTest.cpp - The exact arithmetic bounds rest on --*- C++ -*-===//
// Every soundness bound this repository states is an exact rational, so
// what the header promises — reduced, denominator at least one, no
// negative zero — is what every operation must preserve. That is a
// statement about all inputs, which a corpus of artifacts cannot make.
//
// The canonical form is checked through `str()` rather than through the
// stored magnitudes, which is the right surface: the registry reads the
// spelling, so a value canonical only internally would still be wrong.
//===----------------------------------------------------------------------===//

#include "zkc/Registry/Rational.h"

#include "llvm/Support/Error.h"
#include "ZkcTest.h"

#include <string>

using namespace zkc::registry;

namespace {

uint64_t gcdOf(uint64_t a, uint64_t b) {
  while (b) {
    uint64_t remainder = a % b;
    a = b;
    b = remainder;
  }
  return a;
}

/// The invariant, read off the spelling the registry consumes.
void expectCanonical(const Rational &value, const std::string &where) {
  std::string text = value.str();
  ASSERT_FALSE(text.empty()) << where;
  EXPECT_NE(text, "-0") << where << ": negative zero";
  EXPECT_EQ(text.find("+"), std::string::npos) << where;
  size_t slash = text.find('/');
  if (slash == std::string::npos) {
    EXPECT_EQ(value.denStr(), "1") << where << ": integer with a denominator";
    return;
  }
  std::string numerator = text.substr(0, slash);
  std::string denominator = text.substr(slash + 1);
  EXPECT_NE(denominator, "0") << where;
  EXPECT_NE(denominator, "1") << where << ": denominator one is not spelled";
  EXPECT_EQ(denominator.find('-'), std::string::npos)
      << where << ": sign belongs to the numerator";
  // Small operands throughout, so a machine gcd is exact here.
  if (numerator.size() < 18 && denominator.size() < 18) {
    uint64_t magnitude = std::stoull(
        numerator.front() == '-' ? numerator.substr(1) : numerator);
    EXPECT_EQ(gcdOf(magnitude, std::stoull(denominator)), 1u)
        << where << ": not reduced (" << text << ")";
  }
}

Rational parse(llvm::StringRef text) {
  auto value = Rational::fromDecimal(text);
  if (!value) {
    EXPECT_ADMITTED(std::move(value));
    return Rational();
  }
  return *value;
}

Rational ratio(llvm::StringRef numerator, llvm::StringRef denominator) {
  auto value = Rational::fromDecimalPair(numerator, denominator);
  if (!value) {
    EXPECT_ADMITTED(std::move(value));
    return Rational();
  }
  return *value;
}

TEST(Rational, ReducesWhatItParses) {
  EXPECT_EQ(ratio("2", "4").str(), "1/2");
  EXPECT_EQ(ratio("100", "1000").str(), "1/10");
  EXPECT_EQ(ratio("-3", "9").str(), "-1/3");
  EXPECT_EQ(ratio("8", "4").str(), "2");
  EXPECT_EQ(ratio("0", "7").str(), "0");
  EXPECT_EQ(parse("-0").str(), "0");
  EXPECT_EQ(ratio("4611686018427387904", "2305843009213693952").str(), "2");
}

TEST(Rational, RefusesWhatIsNotAnExactInteger) {
  FOR_EACH(text, (std::initializer_list<llvm::StringRef>{
                     "", "-", "1.5", "1 ", " 1", "+1", "one", "0x10", "1/2",
                     "--1", "01"}))
    EXPECT_REFUSED(Rational::fromDecimal(text));
}

TEST(Rational, RefusesAZeroDenominator) {
  EXPECT_REFUSED(Rational::fromDecimalPair("1", "0"));
}

TEST(Rational, ArithmeticPreservesTheCanonicalForm) {
  const char *operands[] = {"0/1",  "1/1",   "1/2",   "1/3",    "2/7",
                            "-1/2", "-5/11", "13/4",  "1/1024", "6/8"};
  for (const char *leftText : operands)
    for (const char *rightText : operands) {
      llvm::StringRef left(leftText), right(rightText);
      Rational a = ratio(left.split('/').first, left.split('/').second);
      Rational b = ratio(right.split('/').first, right.split('/').second);
      std::string where = left.str() + " and " + right.str();
      expectCanonical(a.add(b), where + " (sum)");
      expectCanonical(a.sub(b), where + " (difference)");
      expectCanonical(a.mul(b), where + " (product)");
      if (!b.isZero()) {
        auto quotient = a.div(b);
        ASSERT_TRUE(static_cast<bool>(quotient)) << where;
        expectCanonical(*quotient, where + " (quotient)");
      }
    }
}

TEST(Rational, AdditionAndSubtractionInvertEachOther) {
  Rational a = ratio("13", "4"), b = ratio("-5", "11");
  EXPECT_EQ(a.add(b).sub(b).compare(a), 0);
  EXPECT_EQ(a.sub(b).add(b).compare(a), 0);
}

TEST(Rational, DivisionByZeroRefusesRatherThanTrapping) {
  EXPECT_REFUSED(ratio("1", "2").div(parse("0")));
}

TEST(Rational, PowerAgreesWithRepeatedMultiplication) {
  for (llvm::StringRef text : {"1/2", "2/3", "3/1", "-1/2", "1/1"})
    for (int64_t exponent = 0; exponent <= 6; ++exponent) {
      Rational base = ratio(text.split('/').first, text.split('/').second);
      auto raised = base.pow(exponent);
      ASSERT_TRUE(static_cast<bool>(raised)) << text.str();
      Rational repeated = parse("1");
      for (int64_t step = 0; step < exponent; ++step)
        repeated = repeated.mul(base);
      EXPECT_EQ(raised->compare(repeated), 0)
          << text.str() << " ^ " << exponent << ": " << raised->str()
          << " against " << repeated.str();
      expectCanonical(*raised, text.str());
    }
}

TEST(Rational, ANegativeExponentInvertsAndRefusesOverZero) {
  auto inverted = ratio("2", "3").pow(-2);
  ASSERT_TRUE(static_cast<bool>(inverted));
  EXPECT_EQ(inverted->str(), "9/4");
  EXPECT_REFUSED(parse("0").pow(-1));
}

TEST(Rational, CompareIsATotalOrder) {
  const char *values[] = {"-5/11", "-1/2", "0/1", "1/1024", "1/3", "1/2",
                          "13/4"};
  for (const char *leftText : values)
    for (const char *rightText : values) {
      llvm::StringRef left(leftText), right(rightText);
      Rational a = ratio(left.split('/').first, left.split('/').second);
      Rational b = ratio(right.split('/').first, right.split('/').second);
      EXPECT_EQ(a.compare(b) < 0, b.compare(a) > 0)
          << left.str() << " against " << right.str();
      EXPECT_EQ(a.compare(b) == 0, left == right);
    }
}

TEST(Rational, CeilLog2RoundsALossUpward) {
  struct Case {
    const char *numerator, *denominator;
    int64_t bits;
  };
  for (const Case &item :
       {Case{"1", "1", 0}, Case{"2", "1", 1}, Case{"3", "1", 2},
        Case{"4", "1", 2}, Case{"5", "1", 3}, Case{"1024", "1", 10},
        Case{"1025", "1", 11}, Case{"1", "2", -1}}) {
    auto bits = ratio(item.numerator, item.denominator).ceilLog2();
    ASSERT_TRUE(static_cast<bool>(bits))
        << item.numerator << "/" << item.denominator;
    EXPECT_EQ(*bits, item.bits)
        << item.numerator << "/" << item.denominator;
  }
  EXPECT_REFUSED(parse("0").ceilLog2());
}

TEST(Rational, FloorAndCeilBracketEveryValue) {
  const char *values[] = {"-7/2", "-1/2", "0/1", "1/2", "7/2", "13/4"};
  for (const char *text : values) {
    llvm::StringRef spelling(text);
    Rational value =
        ratio(spelling.split('/').first, spelling.split('/').second);
    auto low = value.floorToInt();
    auto high = value.ceilToInt();
    ASSERT_TRUE(static_cast<bool>(low)) << text;
    ASSERT_TRUE(static_cast<bool>(high)) << text;
    EXPECT_LE(*low, *high) << text;
    EXPECT_LE(*high - *low, 1) << text;
    EXPECT_LE(Rational::fromInteger(*low).compare(value), 0) << text;
    EXPECT_GE(Rational::fromInteger(*high).compare(value), 0) << text;
  }
}

} // namespace
