#ifndef ZKC_RELATION_AIRPOLYNOMIAL_H
#define ZKC_RELATION_AIRPOLYNOMIAL_H

#include "zkc/Relation/AIR.h"

namespace zkc::relation {

/// Degree analysis for a polynomial interpretation of a finite AIR. Domain
/// points, interpolation and shifted-read adequacy are separate obligations.
/// Padding never changes the original height or active rows here.
struct AIRPolynomialParameters {
  uint32_t height = 0, domainSize = 0, traceDegree = 0;
  static constexpr uint32_t sizeLimit = 1u << 24;
};

struct AIRPolynomialConstraint {
  uint32_t begin = 0, end = 0; // Original active rows, half-open.
  uint32_t selectorDegree = 0; // Complement vanishing polynomial.
  uint64_t numeratorDegree = 0;
  /// No value means an exactly divisible numerator must be zero. An empty
  /// active set is vacuous and has no quotient obligation, irrespective of this
  /// member. A zero polynomial always fits any present bound.
  std::optional<uint64_t> quotientDegree;
  bool active() const { return begin != end; }
};

struct AIRPolynomialAnalysis {
  AIRPolynomialParameters parameters;
  std::vector<AIRPolynomialConstraint> constraints;
  std::vector<AIRCell> reads; // Sorted unique reads of active constraints.
  /// Number of coefficient chunks of length domainSize sufficient for each
  /// individual quotient, and hence for any linear combination of them.
  /// This is not a soundness assertion about random constraint batching.
  uint64_t quotientChunks = 0;
  llvm::json::Value encode() const;
};

/// Work is bounded by relation syntax, independent of height. Unlike the
/// selective evaluator, this does not materialize a per-row schedule.
llvm::Expected<AIRPolynomialAnalysis>
analyzeAIRPolynomials(const AIR &, AIRPolynomialParameters);

} // namespace zkc::relation
#endif
