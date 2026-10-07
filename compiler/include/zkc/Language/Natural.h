#ifndef ZKC_LANGUAGE_NATURAL_H
#define ZKC_LANGUAGE_NATURAL_H
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <map>
#include <string>
#include <vector>

namespace zkc::language {
/// A bounded polynomial over natural atoms. The empty polynomial is zero.
/// Normal forms have nonzero coefficients and sorted, nonempty-identity atoms.
class Natural {
public:
  using Monomial = std::vector<std::string>;
  using Terms = std::map<Monomial, uint64_t>;
  static Natural constant(uint64_t);
  static llvm::Expected<Natural> atom(llvm::StringRef);
  const Terms &terms() const { return polynomial; }
  bool operator==(const Natural &other) const {
    return polynomial == other.polynomial;
  }
  bool operator!=(const Natural &other) const { return !(*this == other); }
  bool isClosed() const;
  uint64_t closedValue() const;
  std::string spelling() const;

private:
  Terms polynomial;
  friend class NaturalArithmetic;
};
/// One budget is shared across normalization and substitution in an invocation.
/// Limits are work bounds, not assumptions about symbolic values.
class NaturalArithmetic {
public:
  explicit NaturalArithmetic(uint64_t work = 1000000, uint64_t terms = 1024,
                             uint64_t factors = 64)
      : remaining(work), termLimit(terms), factorLimit(factors) {}
  llvm::Expected<Natural> add(const Natural &, const Natural &);
  llvm::Expected<Natural> multiply(const Natural &, const Natural &);
  llvm::Expected<Natural> substitute(const Natural &,
                                     const std::map<std::string, Natural> &);
  uint64_t remainingWork() const { return remaining; }

private:
  uint64_t remaining, termLimit, factorLimit;
  llvm::Error charge(uint64_t);
  llvm::Error insert(Natural &, const Natural::Monomial &, uint64_t);
};
} // namespace zkc::language
#endif
