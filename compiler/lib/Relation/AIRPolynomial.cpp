#include "zkc/Relation/AIRPolynomial.h"
#include "zkc/Target/Json.h"
#include <algorithm>
#include <set>

using namespace llvm;
namespace zkc::relation {

Expected<AIRPolynomialAnalysis>
analyzeAIRPolynomials(const AIR &air, AIRPolynomialParameters parameters) {
  const auto [height, domainSize, traceDegree] = parameters;
  if (!height || height > AIRPolynomialParameters::sizeLimit)
    return zkc::error("air-polynomial-height");
  if (domainSize < height || domainSize > AIRPolynomialParameters::sizeLimit)
    return zkc::error("air-polynomial-domain-size");
  // An arbitrary assignment on all domain points needs degree domainSize - 1.
  // Larger bounds permit explicitly selected masking. Special low-degree input
  // relations would need a stronger interpolation contract, not a smaller hint.
  if (traceDegree < domainSize - 1 ||
      traceDegree > AIRPolynomialParameters::sizeLimit)
    return zkc::error("air-polynomial-trace-degree");

  AIRPolynomialAnalysis result{parameters, {}, {}, 0};
  std::set<AIRCell> reads;
  for (size_t i = 0; i < air.constraints().size(); ++i) {
    const auto &constraint = air.constraints()[i];
    const auto &fact = air.facts()[i];
    AIRPolynomialConstraint bound;
    bound.end = height;
    switch (constraint.scope.kind) {
    case AIRScopeKind::Every:
      break;
    case AIRScopeKind::First:
      bound.end = 1;
      break;
    case AIRScopeKind::Last:
      bound.begin = height - 1;
      break;
    case AIRScopeKind::Transition:
      bound.end = height > constraint.scope.lookahead
                      ? height - constraint.scope.lookahead
                      : 0;
      break;
    }
    if (bound.active() && uint64_t(bound.end - 1) + fact.maxOffset >= height)
      return zkc::error("air-window-out-of-range");
    const uint32_t activeRows = bound.end - bound.begin;
    bound.selectorDegree = domainSize - activeRows;
    bound.numeratorDegree = uint64_t(fact.degree) * traceDegree;
    if (bound.numeratorDegree >= activeRows)
      bound.quotientDegree = bound.numeratorDegree - activeRows;
    if (bound.active()) {
      reads.insert(fact.reads.begin(), fact.reads.end());
      if (bound.quotientDegree)
        result.quotientChunks = std::max(
            result.quotientChunks, *bound.quotientDegree / domainSize + 1);
    }
    result.constraints.push_back(bound);
  }
  result.reads.assign(reads.begin(), reads.end());
  return result;
}

json::Value AIRPolynomialAnalysis::encode() const {
  json::Array bounds, footprint;
  for (const auto &c : constraints)
    bounds.push_back(json::Object{
        {"active_begin", c.begin},
        {"active_end", c.end},
        {"active", c.active()},
        {"selector_degree", c.selectorDegree},
        {"numerator_degree", c.numeratorDegree},
        {"quotient_degree", c.quotientDegree ? json::Value(*c.quotientDegree)
                                             : json::Value(nullptr)}});
  for (auto read : reads)
    footprint.push_back(json::Array{read.row, read.column});
  return json::Object{{"schema", "zkc.air-polynomial-analysis/1"},
                      {"height", parameters.height},
                      {"domain_size", parameters.domainSize},
                      {"trace_degree", parameters.traceDegree},
                      {"quotient_chunks", quotientChunks},
                      {"reads", std::move(footprint)},
                      {"constraints", std::move(bounds)}};
}

} // namespace zkc::relation
