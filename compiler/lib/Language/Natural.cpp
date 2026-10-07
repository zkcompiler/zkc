#include "zkc/Language/Natural.h"
#include "zkc/Support/Refusal.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <cassert>
#include <limits>
#include <optional>

using namespace llvm;
namespace zkc::language {
Natural Natural::constant(uint64_t n) {
  Natural value;
  if (n)
    value.polynomial.emplace(Monomial{}, n);
  return value;
}
Expected<Natural> Natural::atom(StringRef name) {
  if (name.empty() || name.size() > 4096 || name.contains('\0'))
    return error("source.natural", "invalid natural atom identity");
  Natural value;
  value.polynomial.emplace(Monomial{{Factor::Kind::Atom, name.str()}}, 1);
  return value;
}
bool Natural::isClosed() const {
  return polynomial.empty() ||
         (polynomial.size() == 1 && polynomial.begin()->first.empty());
}
uint64_t Natural::closedValue() const {
  assert(isClosed());
  return polynomial.empty() ? 0 : polynomial.begin()->second;
}
std::string Natural::spelling() const {
  std::string result;
  raw_string_ostream out(result);
  if (polynomial.empty())
    return "0";
  bool first = true;
  for (const auto &[factors, coefficient] : polynomial) {
    if (!first)
      out << "+";
    first = false;
    out << coefficient;
    for (const auto &factor : factors)
      out << (factor.kind == Factor::Kind::Atom ? "*a" : "*p")
          << factor.name.size() << ":" << factor.name;
  }
  return result;
}
Error NaturalArithmetic::charge(uint64_t work) {
  if (work > remaining)
    return error("source.limit", "natural normalization work limit exceeded");
  remaining -= work;
  return Error::success();
}
Error NaturalArithmetic::insert(Natural &into, const Natural::Monomial &key,
                                uint64_t coefficient) {
  if (auto e = charge(key.size() + 1))
    return e;
  for (auto &factor : key)
    if (auto e = charge(factor.name.size() + 1))
      return e;
  if (!coefficient)
    return Error::success();
  if (key.size() > factorLimit)
    return error("source.limit", "natural monomial degree limit exceeded");
  auto found = into.polynomial.find(key);
  if (found == into.polynomial.end()) {
    if (into.polynomial.size() >= termLimit)
      return error("source.limit", "natural term limit exceeded");
    into.polynomial.emplace(key, coefficient);
  } else {
    if (coefficient > std::numeric_limits<uint64_t>::max() - found->second)
      return error("source.natural", "natural coefficient overflow");
    found->second += coefficient;
  }
  return Error::success();
}
Expected<Natural> NaturalArithmetic::add(const Natural &a, const Natural &b) {
  Natural result;
  for (const auto *value : {&a, &b})
    for (const auto &[factors, coefficient] : value->terms())
      if (auto e = insert(result, factors, coefficient))
        return std::move(e);
  return result;
}
Expected<Natural> NaturalArithmetic::multiply(const Natural &a,
                                              const Natural &b) {
  if (auto e = charge(a.terms().size() + b.terms().size()))
    return std::move(e);
  Natural result;
  for (const auto &[left, x] : a.terms())
    for (const auto &[right, y] : b.terms()) {
      if (auto e = charge(left.size() + right.size() + 1))
        return std::move(e);
      if (left.size() > factorLimit || right.size() > factorLimit - left.size())
        return error("source.limit", "natural monomial degree limit exceeded");
      if (x > std::numeric_limits<uint64_t>::max() / y)
        return error("source.natural", "natural coefficient overflow");
      for (auto *terms : {&left, &right})
        for (auto &factor : *terms)
          if (auto e = charge(factor.name.size() + 1))
            return std::move(e);
      Natural::Monomial factors;
      std::merge(left.begin(), left.end(), right.begin(), right.end(),
                 std::back_inserter(factors));
      if (auto e = insert(result, std::move(factors), x * y))
        return std::move(e);
    }
  return result;
}
Expected<Natural> NaturalArithmetic::powerOfTwo(const Natural &exponent) {
  if (auto e = charge(exponent.terms().size() + 1))
    return std::move(e);
  Natural::Monomial factors;
  uint64_t coefficient = 1;
  for (const auto &[term, count] : exponent.terms()) {
    if (term.empty()) {
      if (count >= 64)
        return error("source.natural", "power of two overflows uint64");
      coefficient = uint64_t{1} << count;
      continue;
    }
    if (term.size() != 1 || term[0].kind != Natural::Factor::Kind::Atom)
      return error("source.natural", "pow2 requires a linear natural exponent");
    if (factors.size() > factorLimit || count > factorLimit - factors.size())
      return error("source.limit", "natural monomial degree limit exceeded");
    // Charge before allocating or copying identities. The division avoids an
    // overflow in the accounting itself, even with caller-selected limits.
    auto identityCost = term[0].name.size() + 1;
    if (count > remaining / identityCost)
      return error("source.limit", "natural normalization work limit exceeded");
    if (auto e = charge(count * identityCost))
      return std::move(e);
    factors.insert(factors.end(), count,
                   {Natural::Factor::Kind::PowerOfTwo, term[0].name});
  }
  Natural result;
  if (auto e = insert(result, factors, coefficient))
    return std::move(e);
  return result;
}
Expected<Natural>
NaturalArithmetic::substitute(const Natural &input,
                              const std::map<std::string, Natural> &bindings) {
  return substitute(input, [&](StringRef name) -> const Natural * {
    auto found = bindings.find(name.str());
    return found == bindings.end() ? nullptr : &found->second;
  });
}
Expected<Natural>
NaturalArithmetic::substitute(const Natural &input,
                              function_ref<const Natural *(StringRef)> lookup) {
  Natural result;
  for (const auto &[factors, coefficient] : input.terms()) {
    Natural term = Natural::constant(coefficient);
    for (const auto &factor : factors) {
      if (auto e = charge(factor.name.size() + 1))
        return std::move(e);
      const Natural *replacement = lookup(factor.name);
      std::optional<Natural> atom;
      if (!replacement) {
        auto identity = Natural::atom(factor.name);
        if (!identity)
          return identity.takeError();
        atom = std::move(*identity);
        replacement = &*atom;
      }
      std::optional<Natural> power;
      if (factor.kind == Natural::Factor::Kind::PowerOfTwo) {
        auto expanded = powerOfTwo(*replacement);
        if (!expanded)
          return expanded.takeError();
        power = std::move(*expanded);
        replacement = &*power;
      }
      auto next = multiply(term, *replacement);
      if (!next)
        return next.takeError();
      term = std::move(*next);
    }
    auto next = add(result, term);
    if (!next)
      return next.takeError();
    result = std::move(*next);
  }
  return result;
}
} // namespace zkc::language
