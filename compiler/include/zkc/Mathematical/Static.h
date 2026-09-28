#ifndef ZKC_MATHEMATICAL_STATIC_H
#define ZKC_MATHEMATICAL_STATIC_H

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <map>
#include <string>
#include <vector>

namespace zkc::mathematical {

/// Shared by all recursive admission work, including substitution, polynomial
/// expansion and closed instance discovery. Exhaustion refuses the whole input.
struct AdmissionBudget {
  size_t remaining = 1000000;
  // Optional invocation-owned account. Copies borrow the same callback, so
  // separate admission and placement phases cannot reset the caller's limit.
  llvm::function_ref<llvm::Error(size_t)> charge = nullptr;
  llvm::Error consume(size_t amount = 1);
};

/// Declaration-local natural expression. This is syntax, not an admitted term;
/// malformed constructor arities and out-of-scope parameters are refused.
struct Static {
  enum class Kind { Literal, Parameter, Add, Multiply, Pow2 };
  Kind kind = Kind::Literal;
  uint64_t value = 0;
  std::vector<Static> operands;

  static Static literal(uint64_t value);
  static Static parameter(uint64_t index);
  static Static add(Static left, Static right);
  static Static multiply(Static left, Static right);
  static Static pow2(Static exponent);
};

/// Sparse natural polynomial. Atoms are scoped parameters or powers of two
/// whose exponents are normalized polynomials. A sorted atom list is a
/// monomial. The representation and constructors are private, so equality is
/// canonical.
class NormalStatic {
public:
  using Monomial = std::vector<std::string>;
  using Terms = std::map<Monomial, uint64_t>;

  bool operator==(const NormalStatic &other) const {
    return terms == other.terms;
  }
  bool operator!=(const NormalStatic &other) const { return !(*this == other); }
  /// Unambiguous canonical spelling for interning, not an interchange encoding.
  llvm::Expected<std::string> key(AdmissionBudget &) const;
  llvm::Expected<uint64_t> closed() const;
  const Terms &polynomial() const { return terms; }

  static NormalStatic literal(uint64_t value);
  static NormalStatic parameter(uint64_t index);

private:
  Terms terms;
  friend llvm::Expected<NormalStatic> normalize(const Static &,
                                                llvm::ArrayRef<NormalStatic>,
                                                AdmissionBudget &, unsigned);
};

/// Substitutes the explicit local parameter environment and normalizes using
/// distributivity/commutativity. pow2 with an open exponent is an atom; further
/// exponential laws require a separate checked derivation. No u64 wraparound.
llvm::Expected<NormalStatic> normalize(const Static &,
                                       llvm::ArrayRef<NormalStatic> parameters,
                                       AdmissionBudget &, unsigned depth = 0);
llvm::Expected<NormalStatic> normalize(const Static &, uint64_t arity,
                                       AdmissionBudget &);
llvm::Expected<uint64_t> evaluate(const Static &, llvm::ArrayRef<uint64_t>,
                                  AdmissionBudget &);

} // namespace zkc::mathematical
#endif
