#include "zkc/Language/Natural.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <limits>
using namespace llvm;
using namespace zkc::language;
namespace {
template <typename T> T take(Expected<T> value) {
  if (!value) {
    errs() << toString(value.takeError()) << "\n";
    std::exit(1);
  }
  return std::move(*value);
}
void check(bool value) {
  if (!value) {
    errs() << "natural check failed\n";
    std::exit(1);
  }
}
template <typename T> void refuses(Expected<T> value, StringRef code) {
  check(!value);
  check(StringRef(toString(value.takeError())).starts_with(code));
}
} // namespace
int main() {
  NaturalArithmetic arithmetic;
  auto n = take(Natural::atom("N")), m = take(Natural::atom("M"));
  auto one = Natural::constant(1), zero = Natural::constant(0);
  auto add = [&](const Natural &a, const Natural &b) {
    return take(arithmetic.add(a, b));
  };
  auto mul = [&](const Natural &a, const Natural &b) {
    return take(arithmetic.multiply(a, b));
  };
  check(add(n, one) == add(one, n));
  check(mul(add(n, one), add(m, one)) == add(add(mul(n, m), n), add(m, one)));
  check(mul(zero, n) == zero);
  check(add(n, n) == mul(Natural::constant(2), n));
  auto closed = take(arithmetic.substitute(
      mul(add(n, one), m),
      {{"N", Natural::constant(4)}, {"M", Natural::constant(3)}}));
  check(closed.isClosed() && closed.closedValue() == 15);
  check(take(arithmetic.substitute(add(n, m), {{"N", m}})) == add(m, m));
  check(n.spelling() != take(Natural::atom("1:N")).spelling());
  auto pow2 = [&](const Natural &value) {
    return take(arithmetic.powerOfTwo(value));
  };
  check(pow2(zero) == one);
  check(pow2(add(n, m)) == mul(pow2(n), pow2(m)));
  check(pow2(add(mul(Natural::constant(2), n), Natural::constant(3))) ==
        mul(Natural::constant(8), mul(pow2(n), pow2(n))));
  check(take(arithmetic.substitute(pow2(n), {{"N", add(m, one)}})) ==
        mul(Natural::constant(2), pow2(m)));
  check(pow2(n).spelling() != take(Natural::atom("pow2(N)")).spelling());
  for (uint64_t a = 0; a < 7; ++a)
    for (uint64_t b = 0; b < 5; ++b) {
      auto expression = add(pow2(add(n, m)), mul(n, pow2(m)));
      auto evaluated = take(
          arithmetic.substitute(expression, {{"N", Natural::constant(a)},
                                             {"M", Natural::constant(b)}}));
      check(evaluated.isClosed());
      check(evaluated.closedValue() ==
            (uint64_t{1} << (a + b)) + a * (uint64_t{1} << b));
    }
  check(pow2(Natural::constant(63)).closedValue() == uint64_t{1} << 63);
  refuses(arithmetic.powerOfTwo(Natural::constant(64)), "source.natural");
  refuses(arithmetic.powerOfTwo(mul(n, n)), "source.natural");
  refuses(arithmetic.powerOfTwo(pow2(n)), "source.natural");
  refuses(arithmetic.substitute(pow2(n), {{"N", mul(m, m)}}), "source.natural");
  refuses(arithmetic.substitute(pow2(n), {{"N", pow2(m)}}), "source.natural");
  NaturalArithmetic boundedPower(1000, 1, 2);
  check(take(boundedPower.powerOfTwo(add(n, m))) == mul(pow2(n), pow2(m)));
  refuses(boundedPower.powerOfTwo(mul(Natural::constant(3), n)),
          "source.limit");
  NaturalArithmetic noPowerWork(0);
  refuses(noPowerWork.powerOfTwo(zero), "source.limit");
  NaturalArithmetic shortIdentities(8);
  refuses(shortIdentities.powerOfTwo(take(Natural::atom("long_natural_name"))),
          "source.limit");
  // Projections are distinct factors: equal only to themselves, retained by
  // substitution of other atoms, decided only by a lookup over the factor.
  auto inputs = take(Natural::projection("A", "Inputs")),
       outputs = take(Natural::projection("A", "Outputs"));
  check(inputs != outputs && inputs != take(Natural::atom("A")) &&
        inputs != take(Natural::atom("A::Inputs")));
  check(inputs.spelling() != outputs.spelling() &&
        inputs.spelling() != take(Natural::atom("A::Inputs")).spelling());
  check(add(inputs, inputs) == mul(Natural::constant(2), inputs));
  check(take(arithmetic.substitute(
            add(inputs, n),
            {{"A", Natural::constant(5)}, {"N", Natural::constant(1)}})) ==
        add(inputs, one));
  check(take(arithmetic.substitute(
            mul(inputs, n), [&](const Natural::Factor &factor) {
              return factor.kind == Natural::Factor::Kind::Projection &&
                             factor.name == "A" && factor.member == "Inputs"
                         ? &m
                         : nullptr;
            })) == mul(m, n));
  refuses(arithmetic.powerOfTwo(inputs), "source.natural");
  refuses(Natural::projection("A", ""), "source.natural");
  refuses(Natural::projection("", "Inputs"), "source.natural");
  unsigned lookups = 0;
  auto borrowed = [&](const Natural::Factor &factor) -> const Natural * {
    ++lookups;
    return factor.name == "N" ? &m : nullptr;
  };
  check(take(arithmetic.substitute(one, borrowed)) == one && lookups == 0);
  check(take(arithmetic.substitute(n, borrowed)) == m && lookups == 1);
  NaturalArithmetic noLookupWork(1);
  refuses(noLookupWork.substitute(n, borrowed), "source.limit");
  check(lookups == 1);
  NaturalArithmetic insufficientCopyWork(8);
  auto largeBinding = take(Natural::atom("large_borrowed_natural_parameter"));
  refuses(insufficientCopyWork.substitute(
              n, [&](const Natural::Factor &) { return &largeBinding; }),
          "source.limit");
  auto maximum = Natural::constant(std::numeric_limits<uint64_t>::max());
  refuses(arithmetic.add(maximum, one), "source.natural");
  refuses(arithmetic.multiply(maximum, Natural::constant(2)), "source.natural");
  auto cancel = [&](const Natural &a, const Natural &b) {
    return take(arithmetic.cancelCommonTerms(a, b));
  };
  auto residuals = [&](const Natural &a, const Natural &b, const Natural &left,
                       const Natural &right) {
    check(cancel(a, b) == std::make_pair(left, right));
    check(cancel(b, a) == std::make_pair(right, left));
  };
  residuals(zero, zero, zero, zero);
  residuals(n, n, zero, zero);
  residuals(add(add(n, m), one), add(add(m, n), inputs), one, inputs);
  residuals(add(mul(Natural::constant(3), n), one),
            add(mul(Natural::constant(2), n), m), add(n, one), m);
  // Identical nonlinear terms are additive quantities, even when they vanish.
  auto nonlinear = add(mul(n, m), mul(n, n));
  residuals(add(nonlinear, one), add(nonlinear, m), one, m);
  residuals(add(pow2(n), inputs), add(pow2(n), outputs), inputs, outputs);
  residuals(pow2(n), n, pow2(n), n);
  residuals(inputs, take(Natural::atom("A::Inputs")), inputs,
            take(Natural::atom("A::Inputs")));
  residuals(n, take(Natural::atom("other::N")), n,
            take(Natural::atom("other::N")));
  // No division by a shared factor: N may be zero, and N*M is not M.
  residuals(mul(n, m), mul(n, inputs), mul(n, m), mul(n, inputs));
  residuals(zero, mul(n, m), zero, mul(n, m));
  auto almostMaximum =
      Natural::constant(std::numeric_limits<uint64_t>::max() - 1);
  residuals(maximum, one, almostMaximum, zero);
  residuals(add(maximum, mul(maximum, n)),
            add(almostMaximum, mul(almostMaximum, n)), add(one, n), zero);
  residuals(add(maximum, mul(one, n)), add(one, mul(maximum, n)), almostMaximum,
            mul(almostMaximum, n));
  NaturalArithmetic cancellationBudget;
  auto beforeCancellation = cancellationBudget.remainingWork();
  check(take(cancellationBudget.cancelCommonTerms(nonlinear, nonlinear)) ==
        std::make_pair(zero, zero));
  auto cancellationCost =
      beforeCancellation - cancellationBudget.remainingWork();
  check(cancellationCost > 0);
  NaturalArithmetic exactCancellationWork(cancellationCost);
  take(exactCancellationWork.cancelCommonTerms(nonlinear, nonlinear));
  check(exactCancellationWork.remainingWork() == 0);
  refuses(exactCancellationWork.cancelCommonTerms(zero, zero), "source.limit");
  NaturalArithmetic insufficientCancellationWork(cancellationCost - 1);
  refuses(insufficientCancellationWork.cancelCommonTerms(nonlinear, nonlinear),
          "source.limit");
  NaturalArithmetic cancellationNames(8);
  refuses(cancellationNames.cancelCommonTerms(largeBinding, largeBinding),
          "source.limit");
  NaturalArithmetic cancellationTerms(1000, 1);
  refuses(cancellationTerms.cancelCommonTerms(add(n, m), add(n, m)),
          "source.limit");
  NaturalArithmetic cancellationFactors(1000, 2, 1);
  refuses(cancellationFactors.cancelCommonTerms(mul(n, m), mul(n, m)),
          "source.limit");
  NaturalArithmetic exactly(100, 2, 2);
  check(take(exactly.add(n, m)).terms().size() == 2);
  refuses(exactly.add(add(n, m), one), "source.limit");
  check(take(exactly.multiply(n, n)).terms().begin()->first.size() == 2);
  refuses(exactly.multiply(mul(n, n), n), "source.limit");
  NaturalArithmetic noWork(0);
  refuses(noWork.add(n, zero), "source.limit");
  NaturalArithmetic oneTerm(100, 1);
  refuses(oneTerm.multiply(add(n, one), add(n, one)), "source.limit");
  refuses(Natural::atom(""), "source.natural");
  outs() << "bounded natural normalization checks passed\n";
}
