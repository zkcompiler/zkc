#include "zkc/Language/Natural.h"
#include "zkc/Support/Refusal.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <cassert>
#include <limits>

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
  value.polynomial.emplace(Monomial{name.str()}, 1);
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
      out << "*" << factor.size() << ":" << factor;
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
    if (auto e = charge(factor.size()))
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
          if (auto e = charge(factor.size()))
            return std::move(e);
      Natural::Monomial factors;
      std::merge(left.begin(), left.end(), right.begin(), right.end(),
                 std::back_inserter(factors));
      if (auto e = insert(result, std::move(factors), x * y))
        return std::move(e);
    }
  return result;
}
Expected<Natural>
NaturalArithmetic::substitute(const Natural &input,
                              const std::map<std::string, Natural> &bindings) {
  Natural result;
  for (const auto &[factors, coefficient] : input.terms()) {
    Natural term = Natural::constant(coefficient);
    for (const auto &factor : factors) {
      if (auto e = charge(1))
        return std::move(e);
      auto found = bindings.find(factor);
      auto atom = Natural::atom(factor);
      if (!atom)
        return atom.takeError();
      auto next =
          multiply(term, found == bindings.end() ? *atom : found->second);
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
