#include "zkc/Analysis/Obligations.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <string>

using namespace zkc::analysis;

namespace {
void require(bool condition, const char *message) {
  if (!condition) {
    llvm::errs() << message << '\n';
    std::exit(1);
  }
}
void succeeds(llvm::Error result) {
  if (result) {
    llvm::errs() << llvm::toString(std::move(result)) << '\n';
    std::exit(1);
  }
}
void refuses(llvm::Error result, llvm::StringRef code) {
  require(bool(result), "unexpected acceptance");
  require(llvm::toString(std::move(result)) == code, "wrong refusal code");
}
} // namespace

int main() {
  // Two independent component facts feed a shared residual and an application
  // requirement. Rule order deliberately differs from dependency order.
  std::vector<ReductionRule> rules{{{2, 1}, 3}, {{0, 1}, 2}};
  auto derived = deriveObligations(4, {3}, {0, 1}, rules);
  if (!derived) {
    llvm::errs() << llvm::toString(derived.takeError()) << '\n';
    return 1;
  }
  require(*derived == ObligationCertificate({1, 0}), "wrong derivation order");
  succeeds(checkObligations(4, {3, 3, 2}, {0, 1}, rules, *derived));
  refuses(checkObligations(4, {3}, {0, 1}, rules, {}), "claim-unresolved");
  refuses(checkObligations(4, {3}, {0, 1}, rules, {0, 1}),
          "claim-premise-unavailable");
  refuses(checkObligations(4, {3}, {0, 1}, rules, {2}), "claim-rule-index");
  refuses(checkObligations(4, {3, 3, 2}, {3}, {}, {}), "claim-unresolved");
  refuses(checkObligations(4, {3}, {0, 2}, rules, {1, 0}),
          "claim-premise-unavailable");
  refuses(checkObligations(4, {4}, {}, {}, {}), "claim-index");
  refuses(checkObligations(4, {}, {}, {{{4}, 0}}, {}), "claim-index");
  refuses(checkObligations(4, {}, {}, {{{}, 4}}, {}), "claim-index");
  refuses(checkObligations((1U << 20) + 1, {}, {}, {}, {}),
          "claim-analysis-limit");

  auto cycle = deriveObligations(2, {0}, {}, {{{0}, 1}, {{1}, 0}});
  require(!cycle, "unseeded cycle accepted");
  refuses(cycle.takeError(), "claim-unresolved");
  auto shared = deriveObligations(3, {1, 2}, {0, 0}, {{{0, 0}, 1}, {{0}, 2}});
  require(bool(shared), "shared and duplicate premises rejected");
  succeeds(checkObligations(3, {1, 2}, {0}, {{{0, 0}, 1}, {{0}, 2}}, *shared));
  auto closed = deriveObligations(2, {1}, {}, {{{}, 0}, {{0}, 1}});
  require(bool(closed), "admitted premise-free rule rejected");
  succeeds(checkObligations(2, {1}, {}, {{{}, 0}, {{0}, 1}}, *closed));
  succeeds(checkObligations(0, {}, {}, {}, {}));

  // A small rule table must not amplify checking work without a bound.
  std::vector<ReductionRule> wide{{std::vector<ClaimId>(4096, 0), 1}};
  ObligationCertificate repeated(1024, 0);
  succeeds(checkObligations(2, {1}, {0}, wide, repeated));
  repeated.push_back(0);
  refuses(checkObligations(2, {1}, {0}, wide, repeated),
          "claim-analysis-limit");

  // Exhaust all two-claim single-premise graphs and terminal/requirement sets.
  // Independent least-fixed-point oracle does not use certificate order.
  for (unsigned graph = 0; graph < 16; ++graph) {
    std::vector<ReductionRule> edges;
    for (unsigned from = 0; from < 2; ++from)
      for (unsigned to = 0; to < 2; ++to)
        if (graph & (1U << (2 * from + to)))
          edges.push_back({{from}, to});
    for (unsigned seeds = 0; seeds < 4; ++seeds) {
      std::vector<ClaimId> facts;
      for (unsigned id = 0; id < 2; ++id)
        if (seeds & (1U << id))
          facts.push_back(id);
      unsigned reachable = seeds, previous;
      do {
        previous = reachable;
        for (const auto &edge : edges)
          if (reachable & (1U << edge.premises.front()))
            reachable |= 1U << edge.conclusion;
      } while (reachable != previous);
      for (unsigned demands = 0; demands < 4; ++demands) {
        std::vector<ClaimId> required;
        for (unsigned id = 0; id < 2; ++id)
          if (demands & (1U << id))
            required.push_back(id);
        auto candidate = deriveObligations(2, required, facts, edges);
        require(bool(candidate) == ((reachable & demands) == demands),
                "fixed-point disagreement");
        if (candidate)
          succeeds(checkObligations(2, required, facts, edges, *candidate));
        else
          llvm::consumeError(candidate.takeError());
      }
    }
  }
  llvm::outs()
      << "obligation closure controls and 256 fixed-point cases passed\n";
}
