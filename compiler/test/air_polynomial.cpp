#include "zkc/Relation/AIRPolynomial.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace zkc::relation;

static void require(bool condition, StringRef message) {
  if (!condition) {
    errs() << message << '\n';
    std::exit(1);
  }
}
template <typename T> static T value(Expected<T> result) {
  if (!result) {
    errs() << toString(result.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*result);
}
template <typename T> static void refuses(Expected<T> result, StringRef code) {
  require(!result, "expected refusal");
  require(toString(result.takeError()) == code, "wrong refusal");
}

int main() {
  using N = AIRNode;
  const std::vector<N> square{N::read(0, 0), N::mul(0, 0)};
  const auto air =
      value(AIR::create("koala-bear", 1, 0,
                        {{{AIRScopeKind::Every, 0}, square, {}, {}},
                         {{AIRScopeKind::First, 0}, square, {}, {}},
                         {{AIRScopeKind::Last, 0}, square, {}, {}},
                         {{AIRScopeKind::Transition, 2}, square, {}, {}}}));
  const auto analysis = value(analyzeAIRPolynomials(air, {4, 4, 3}));
  // Degree-six numerators have quotient degrees 2,5,5,4. First/last and
  // lookahead-two constraints require TWO chunks, contrary to the d-1 rule.
  require(analysis.quotientChunks == 2, "selector-aware quotient split");
  const uint64_t expected[] = {2, 5, 5, 4};
  for (unsigned i = 0; i < 4; ++i)
    require(analysis.constraints[i].quotientDegree == expected[i],
            "per-scope divisor degree");
  require(analysis.reads == std::vector<AIRCell>{{0, 0}},
          "shared read footprint");

  const auto padded = value(analyzeAIRPolynomials(air, {3, 4, 3}));
  require(padded.constraints[2].begin == 2 && padded.constraints[2].end == 3,
          "padding must retain original last row");
  require(padded.constraints[0].selectorDegree == 1 &&
              padded.constraints[3].end == 1,
          "padding cannot add constraints on padding rows");
  const auto masked = value(analyzeAIRPolynomials(air, {4, 4, 6}));
  require(masked.quotientChunks == 3, "masking increases degree budget");

  const auto constant = value(
      AIR::create("koala-bear", 0, 0,
                  {{{AIRScopeKind::Every, 0}, {N::constant("1")}, {}, {}}}));
  const auto zeroOnly = value(analyzeAIRPolynomials(constant, {4, 4, 3}));
  require(
      !zeroOnly.constraints[0].quotientDegree && !zeroOnly.quotientChunks,
      "low-degree divisible numerator must be zero; not proof of satisfaction");

  const auto empty = value(
      AIR::create("koala-bear", 1, 0,
                  {{{AIRScopeKind::Transition, 4}, {N::read(4, 0)}, {}, {}}}));
  const auto vacuous = value(analyzeAIRPolynomials(empty, {4, 4, 3}));
  require(!vacuous.constraints[0].active() && vacuous.reads.empty() &&
              !vacuous.quotientChunks,
          "empty active set has no quotient or opening obligation");
  const auto wrapping =
      value(AIR::create("koala-bear", 1, 0,
                        {{{AIRScopeKind::Every, 0}, {N::read(1, 0)}, {}, {}}}));
  refuses(analyzeAIRPolynomials(wrapping, {4, 4, 3}),
          "air-window-out-of-range");
  refuses(analyzeAIRPolynomials(air, {0, 4, 3}), "air-polynomial-height");
  refuses(analyzeAIRPolynomials(air,
                                {AIRPolynomialParameters::sizeLimit + 1, 4, 3}),
          "air-polynomial-height");
  refuses(analyzeAIRPolynomials(air, {4, 3, 3}), "air-polynomial-domain-size");
  refuses(analyzeAIRPolynomials(air,
                                {4, AIRPolynomialParameters::sizeLimit + 1, 3}),
          "air-polynomial-domain-size");
  refuses(analyzeAIRPolynomials(air, {4, 4, 2}), "air-polynomial-trace-degree");
  refuses(analyzeAIRPolynomials(air,
                                {4, 4, AIRPolynomialParameters::sizeLimit + 1}),
          "air-polynomial-trace-degree");
  // This analysis must not materialize millions of row invocations or inherit
  // the selective evaluator's much smaller schedule limit.
  const auto large =
      value(analyzeAIRPolynomials(air, {1 << 23, 1 << 23, (1 << 23) - 1}));
  require(large.quotientChunks == 2 && large.constraints.size() == 4,
          "analysis scales with syntax, not trace height");
  outs() << "AIR polynomial bounds and semantic controls pass\n";
}
