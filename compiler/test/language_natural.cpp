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
