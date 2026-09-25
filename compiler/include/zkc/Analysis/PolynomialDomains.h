#ifndef ZKC_ANALYSIS_POLYNOMIALDOMAINS_H
#define ZKC_ANALYSIS_POLYNOMIALDOMAINS_H

#include "zkc/Source/Execution.h"
#include "llvm/Support/JSON.h"
#include <optional>

namespace zkc {

/// Hash-consed exact expressions. Value leaves name Execution SSA occurrences;
/// length is exact even when its numeric value is unknown. Half and square
/// express the successful even/odd domain map. No may-dependency is an
/// equality.
struct DomainTerm {
  std::string kind, type, atom;
  std::vector<unsigned> arguments;
};
struct PolynomialDomain {
  std::string path, operation, role, field, convention;
  std::string association, shiftOrigin, sizeOrigin;
  bool sizeOriginIsLength = false;
  unsigned shift, size;
  std::optional<unsigned> congruenceClass;
};
struct DomainComparison {
  enum class Result { Same, Different, Unknown } result = Result::Unknown;
  std::vector<std::string> reasons;
};
struct DomainUse {
  std::string value;
  unsigned domain;
  std::optional<unsigned> producerDomain;
  DomainComparison compatibility;
};
struct PolynomialDomains {
  source::Execution execution;
  std::vector<DomainTerm> terms;
  std::vector<PolynomialDomain> domains;
  std::vector<DomainUse> uses;
  /// Only positive vector-result associations. A coefficient polynomial is
  /// reusable on unrelated domains and acquires no persistent coset identity.
  std::map<std::string, unsigned> vectorDomains;
};

/// Admitted finite occurrences only. Facts are conditional on successful
/// operations under their installed contracts; no native adequacy theorem,
/// low-degree, acceptance, security, or rewrite permission is supplied.
PolynomialDomains analyzePolynomialDomains(source::Execution);
llvm::Expected<PolynomialDomains>
inspectPolynomialDomains(const source::Module &, llvm::StringRef entry);
/// Compare ordered nominal domains, not equality of unordered point sets.
/// Distinct dynamic value origins alone establish neither equality nor
/// inequality.
DomainComparison comparePolynomialDomains(const PolynomialDomains &,
                                          unsigned left, unsigned right);
llvm::json::Value encodePolynomialDomains(const PolynomialDomains &);
llvm::json::Value encodeDomainComparison(const DomainComparison &);

} // namespace zkc
#endif
