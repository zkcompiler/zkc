#ifndef ZKC_RELATION_BUNDLEPOLYNOMIAL_H
#define ZKC_RELATION_BUNDLEPOLYNOMIAL_H

#include "zkc/Relation/AIRPolynomial.h"
#include "zkc/Relation/Bundle.h"

namespace zkc::relation {

/// Polynomial interpretation of one present bundle table, derived from the
/// admitted Bundle's facts under the finite-scope law shared with
/// AIRPolynomial.h. Every column of a group denotes an interpolation
/// polynomial T of degree at most traceDegree over distinct domain points for
/// the rows, a read at signed offset k denotes T(g^k X), and an assertion on
/// scope S requires its numerator to be divisible by the vanishing polynomial
/// of S. Degrees count every read as one and every public slot as zero,
/// irrespective of the group's authority, exactly as the Bundle facts do.
///
/// The view describes one table in isolation. It claims nothing about
/// interactions, other tables, optional presence, whole-Bundle satisfaction,
/// random batching of assertions or any commitment or proof protocol.

/// TwoAdicNatural is the selected initial profile: height = domainSize = n
/// for a power of two n >= 2, traceDegree = n - 1, and row i at the i-th power
/// of the installed two-adic root of order n in the carrier's prime subfield.
/// Any other checked parameters are General.
enum class BundlePolynomialProfile { TwoAdicNatural, General };

struct BundlePolynomialGroup {
  std::string name;
  BundleAuthority authority = BundleAuthority::Witness;
  std::string field;
  uint32_t width = 1;
  /// Sorted distinct signed offsets read by active assertions. A cyclic read
  /// wraps in the height domain; a finite read is defined only on its scope.
  std::vector<int32_t> offsets;
};
struct BundlePolynomialAssertion {
  uint32_t output = 0;
  BundleScope scope;
  uint32_t degree = 0;           // The output's read-degree fact.
  AIRPolynomialConstraint bound; // Active rows and the scoped quotient bound.
};
struct BundlePolynomialView {
  std::string relation; // Bundle identity.
  uint32_t table = 0;
  std::string name;
  std::string field; // Carrier; every subject has this field.
  unsigned coordinates = 1;
  bool optional = false;
  BundleHeight heightPolicy;
  BundleReadModel readModel = BundleReadModel::Finite;
  AIRPolynomialParameters parameters;
  BundlePolynomialProfile profile = BundlePolynomialProfile::General;
  std::vector<BundlePolynomialGroup> groups; // Declaration order.
  /// One per arena input, in order. Evaluating only active outputs requests
  /// exactly the bindings whose read or public slot is listed below; the
  /// others are never read.
  std::vector<BundleInput> bindings;
  std::vector<uint32_t> publics; // Sorted public slots of active assertions.
  std::vector<BundleRead> reads; // Sorted distinct reads of active assertions.
  std::vector<BundlePolynomialAssertion> assertions; // Declaration order.
  uint32_t activeAssertions = 0;
  /// Largest present quotient bound over active assertions.
  std::optional<uint64_t> maxQuotientDegree;
  /// Coefficient chunks of length domainSize sufficient for each individual
  /// active quotient, and hence for any linear combination of them. This is
  /// not a soundness assertion about random assertion batching.
  uint64_t quotientChunks = 0;
  /// Identity of the table arena, the one subject every assertion output
  /// refers to. The arena itself stays borrowed from the admitted Bundle.
  std::string arena;
  /// Deterministic `zkc.relation-bundle-polynomial-analysis/0` encoding.
  llvm::json::Value encode() const;
};

/// Parameters of the TwoAdicNatural profile at height n
/// (`bundle-polynomial-two-adic` unless n is a power of two in [2, sizeLimit]).
llvm::Expected<AIRPolynomialParameters>
twoAdicPolynomialParameters(uint32_t height);

/// Table index and carrier homogeneity as for `bundleTableView`, then the
/// shared parameter law, the table's height policy (`bundle-height`), the
/// domain rule and every assertion window at the height
/// (`bundle-scope-height`, `bundle-window`), in that order. A cyclic table
/// needs the wrap law T(g^k X) on every row, so it requires height ==
/// domainSize with a two-adic height admitted by the carrier
/// (`bundle-polynomial-domain`); a finite table may pad the domain beyond its
/// height, which never adds active rows. Work is bounded by the Bundle's
/// retained facts, independent of the height.
llvm::Expected<BundlePolynomialView>
analyzeBundlePolynomials(const Bundle &, uint32_t table,
                         llvm::StringRef carrier, AIRPolynomialParameters);

/// The viewed table's arena, re-derived from the admitted Bundle. A view of
/// another bundle or table is refused (`bundle-polynomial-relation`); the
/// view is descriptive and never a replacement subject.
llvm::Expected<const ring::Expression *>
bundlePolynomialArena(const Bundle &, const BundlePolynomialView &);

} // namespace zkc::relation
#endif
