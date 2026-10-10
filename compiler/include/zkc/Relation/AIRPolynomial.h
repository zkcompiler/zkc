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

/// The parameter law shared by the finite AIR analysis and the bundle
/// polynomial view: height in [1, sizeLimit], domainSize in [height,
/// sizeLimit] and traceDegree in [domainSize - 1, sizeLimit]
/// (`air-polynomial-height`, `air-polynomial-domain-size`,
/// `air-polynomial-trace-degree`).
llvm::Error checkAIRPolynomialParameters(AIRPolynomialParameters);
/// The scoped quotient law for one check of conservative degree `degree`
/// whose active original rows are [begin, end) under checked parameters:
/// selector degree domainSize - |S|, numerator degree degree * traceDegree,
/// and quotient degree numerator - |S| exactly when the numerator reaches |S|.
/// The complement form numerator + selector - domainSize agrees. Window
/// adequacy of the active rows is the caller's obligation.
AIRPolynomialConstraint scopedQuotientBound(AIRPolynomialParameters,
                                            uint32_t begin, uint32_t end,
                                            uint32_t degree);
/// Coefficient chunks of length domainSize that hold one quotient of this
/// degree: the block split Q(X) = sum_k X^(k*domainSize) Q_k(X).
inline uint64_t quotientChunkCount(uint64_t quotientDegree,
                                   uint32_t domainSize) {
  return quotientDegree / domainSize + 1;
}

/// Work is bounded by relation syntax, independent of height. Unlike the
/// selective evaluator, this does not materialize a per-row schedule.
llvm::Expected<AIRPolynomialAnalysis>
analyzeAIRPolynomials(const AIR &, AIRPolynomialParameters);

} // namespace zkc::relation
#endif
