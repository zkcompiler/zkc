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
void refuses(Expected<Natural> value, StringRef code) {
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
  unsigned lookups = 0;
  auto borrowed = [&](StringRef name) -> const Natural * {
    ++lookups;
    return name == "N" ? &m : nullptr;
  };
  check(take(arithmetic.substitute(one, borrowed)) == one && lookups == 0);
  check(take(arithmetic.substitute(n, borrowed)) == m && lookups == 1);
  NaturalArithmetic noLookupWork(1);
  refuses(noLookupWork.substitute(n, borrowed), "source.limit");
  check(lookups == 1);
  NaturalArithmetic insufficientCopyWork(8);
  auto largeBinding = take(Natural::atom("large_borrowed_natural_parameter"));
  refuses(insufficientCopyWork.substitute(
              n, [&](StringRef) { return &largeBinding; }),
          "source.limit");
  auto maximum = Natural::constant(std::numeric_limits<uint64_t>::max());
  refuses(arithmetic.add(maximum, one), "source.natural");
  refuses(arithmetic.multiply(maximum, Natural::constant(2)), "source.natural");
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
