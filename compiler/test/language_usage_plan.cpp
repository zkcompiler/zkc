#include "../lib/Language/UsagePlan.h"
#include "support/NativeCases.h"
#include <random>
using namespace zkc::language;
using namespace zkc::test;
namespace source = zkc::language::detail;
namespace {
struct Environment {
  Limits limits;
  source::Work work{limits};
  std::vector<Declaration> declarations{Declaration{}};
  source::Semantics semantics{declarations, {}, work};
  source::UsagePlan plan{semantics, declarations.front()};
  Type parameter{Type::Kind::Parameter, "T"};
  std::set<std::pair<std::string, source::Usage>> requirements;
  void solve() {
    require(plan.solve([&](const Type &type, source::Usage usage, Span,
                           llvm::StringRef, llvm::StringRef) {
      requirements.emplace(spelling(type), usage);
      return true;
    }),
            "usage planning failed");
    if (semantics.diagnostic)
      throw std::runtime_error("usage planning diagnostic");
  }
  bool needs(source::Usage usage) const {
    return requirements.count({spelling(parameter), usage});
  }
};
} // namespace
int main() {
  using Plan = source::UsagePlan;
  using Usage = source::Usage;
  Cases cases;
  cases.run("exclusive forwards do not duplicate or drop", [] {
    Environment e;
    auto value = e.plan.own(e.parameter, {}, Plan::always);
    auto branch = e.plan.branch(3);
    for (unsigned i = 0; i < 3; ++i)
      require(e.plan.use(value, {}, e.plan.arm(branch, i, {}), {}), "use");
    require(e.plan.finish(value, Plan::always, {}, false), "finish");
    e.solve();
    require(e.requirements.empty(), "exclusive forwarding added a requirement");
  });
  cases.run("unused continuing arm requires Drop", [] {
    Environment e;
    auto value = e.plan.own(e.parameter, {}, Plan::always);
    auto branch = e.plan.branch(2);
    e.plan.use(value, {}, e.plan.arm(branch, 0, {}), {});
    e.plan.finish(value, Plan::always, {}, false);
    e.solve();
    require(e.needs(Usage::Drop) && !e.needs(Usage::Copy), "branch Drop");
  });
  cases.run("stopped arm waives Drop but never earlier duplication", [] {
    Environment e;
    auto value = e.plan.own(e.parameter, {}, Plan::always);
    auto branch = e.plan.branch(2);
    auto continued = e.plan.arm(branch, 0, {});
    auto stopped = e.plan.arm(branch, 1, {});
    e.plan.use(value, {}, continued, {});
    e.plan.use(value, {}, stopped, {});
    e.plan.use(value, {}, stopped, {});
    e.plan.finish(value, continued, {}, false);
    e.solve();
    require(e.needs(Usage::Copy) && !e.needs(Usage::Drop), "stopped prefix");
  });
  cases.run("state transport retains authored consumption history", [] {
    Environment e;
    auto value = e.plan.own(e.parameter, {}, Plan::always);
    auto branch = e.plan.branch(2);
    Plan::Value joined;
    for (unsigned i = 0; i < 2; ++i) {
      auto guard = e.plan.arm(branch, i, {});
      auto state = e.plan.within(value, guard, {});
      e.plan.use(state, {}, guard, {});
      joined.insert(joined.end(), state.begin(), state.end());
    }
    e.plan.finish(joined, Plan::always, {}, false);
    e.solve();
    require(e.requirements.empty(), "unused transport duplicated state");
    e.plan.use(joined, {}, Plan::always, {});
    e.requirements.clear();
    e.solve();
    require(e.needs(Usage::Copy), "a later authored use needs Copy");
  });
  cases.run("early completion cannot borrow a later continuation use", [] {
    Environment e;
    auto value = e.plan.own(e.parameter, {}, Plan::always);
    e.plan.finish(value, Plan::always, {}, true);
    e.plan.use(value, {}, Plan::always, {});
    e.solve();
    require(e.needs(Usage::Drop), "early obligation was lost");
  });
  cases.run("disjoint fields move independently", [] {
    Environment e;
    Type tuple(Type::Kind::Tuple);
    tuple.arguments = {e.parameter, e.parameter};
    auto value = e.plan.own(tuple, {}, Plan::always);
    e.plan.use(value, {0}, Plan::always, {});
    e.plan.use(value, {1}, Plan::always, {});
    e.plan.finish(value, Plan::always, {}, false);
    e.solve();
    require(e.requirements.empty(), "disjoint fields overlap");
  });
  cases.run("a whole use overlaps an earlier field", [] {
    Environment e;
    Type tuple(Type::Kind::Tuple);
    tuple.arguments = {e.parameter, Type{}};
    auto value = e.plan.own(tuple, {}, Plan::always);
    e.plan.use(value, {0}, Plan::always, {});
    e.plan.use(value, {}, Plan::always, {});
    e.plan.finish(value, Plan::always, {}, false);
    e.solve();
    require(e.needs(Usage::Copy), "whole use missed a moved field");
  });
  cases.run("nested branch guards preserve exhaustiveness", [] {
    Environment e;
    auto value = e.plan.own(e.parameter, {}, Plan::always);
    auto outer = e.plan.branch(2), inner = e.plan.branch(3);
    for (unsigned i = 0; i < 3; ++i) {
      auto guard = e.plan.intersect(e.plan.arm(outer, 0, {}),
                                    e.plan.arm(inner, i, {}), {});
      e.plan.use(value, {}, guard, {});
    }
    e.plan.use(value, {}, e.plan.arm(outer, 1, {}), {});
    e.plan.finish(value, Plan::always, {}, false);
    e.solve();
    require(e.requirements.empty(), "nested branches lost coverage");
  });
  cases.run("joined successors remember partial moves", [] {
    Environment e;
    Type tuple(Type::Kind::Tuple);
    tuple.arguments = {e.parameter, e.parameter};
    auto value = e.plan.own(tuple, {}, Plan::always);
    e.plan.use(value, {0}, Plan::always, {});
    auto joined = e.plan.join(value, {});
    e.plan.use(joined, {1}, Plan::always, {});
    e.solve();
    require(e.needs(Usage::Copy), "whole successor lost partial consumption");
  });
  cases.run("an unused joined successor adds no Copy", [] {
    Environment e;
    Type tuple(Type::Kind::Tuple);
    tuple.arguments = {e.parameter, e.parameter};
    auto value = e.plan.own(tuple, {}, Plan::always);
    e.plan.use(value, {0}, Plan::always, {});
    e.plan.join(value, {});
    e.solve();
    require(!e.needs(Usage::Copy), "unused successor required Copy");
  });
  cases.run("shared guard diagrams stay bounded", [] {
    Environment e;
    auto value = e.plan.own(e.parameter, {}, Plan::always);
    auto continuing = Plan::always;
    for (unsigned i = 0; i < 40; ++i) {
      auto branch = e.plan.branch(3);
      auto arms = e.plan.unite(e.plan.arm(branch, 0, {}),
                               e.plan.arm(branch, 1, {}), {});
      continuing = e.plan.intersect(continuing, arms, {});
    }
    e.plan.finish(value, continuing, {}, false);
    e.solve();
    require(e.needs(Usage::Drop), "nonempty continuing guard disappeared");
  });
  cases.run("sequential guards do not consume expression nesting", [] {
    Environment e;
    e.limits.expressionDepth = 8;
    auto value = e.plan.own(e.parameter, {}, Plan::always);
    auto continuing = Plan::always;
    for (unsigned i = 0; i < 40; ++i) {
      auto branch = e.plan.branch(2);
      continuing = e.plan.intersect(continuing, e.plan.arm(branch, 0, {}), {});
    }
    e.plan.use(value, {}, continuing, {});
    e.plan.finish(value, continuing, {}, false);
    e.solve();
    require(e.requirements.empty(), "sequential guard coverage differs");
  });
  cases.run("repeated uses of one path aggregate their guards", [] {
    Environment e;
    auto value = e.plan.own(e.parameter, {}, Plan::always);
    for (unsigned i = 0; i < 4000; ++i)
      e.plan.use(value, {}, Plan::always, {});
    e.solve();
    require(e.needs(Usage::Copy), "repetition lost Copy");
  });
  cases.run("disjoint aggregate uses fit a linear work budget", [] {
    for (bool concrete : {false, true}) {
      Environment e;
      e.limits.work = 100000;
      Type array(Type::Kind::Array);
      array.arguments = {concrete ? Type{} : e.parameter};
      array.dimension = Natural::constant(1024);
      auto value = e.plan.own(array, {}, Plan::always);
      for (unsigned i = 0; i < 1024; ++i)
        require(e.plan.use(value, {i}, Plan::always, {}), "field use");
      require(e.plan.finish(value, Plan::always, {}, false), "finish");
      e.solve();
      require(e.requirements.empty(), "disjoint array elements gained usage");
    }
  });
  cases.run("guard operations agree with finite truth tables", [] {
    Environment e;
    std::vector<std::pair<Plan::Guard, uint64_t>> expressions{
        {Plan::never, 0}, {Plan::always, ~uint64_t(0)}};
    std::vector<unsigned> branches;
    for (unsigned variable = 0; variable < 6; ++variable) {
      auto branch = e.plan.branch(2);
      branches.push_back(branch);
      uint64_t truth = 0;
      for (unsigned assignment = 0; assignment < 64; ++assignment)
        if (assignment & (1u << variable))
          truth |= uint64_t(1) << assignment;
      expressions.emplace_back(e.plan.arm(branch, 1, {}), truth);
    }
    std::vector<Plan::Guard> assignments;
    for (unsigned assignment = 0; assignment < 64; ++assignment) {
      auto guard = Plan::always;
      for (unsigned variable = 0; variable < 6; ++variable)
        guard = e.plan.intersect(
            guard,
            e.plan.arm(branches[variable], (assignment >> variable) & 1, {}),
            {});
      assignments.push_back(guard);
    }
    std::minstd_rand random(7);
    for (unsigned i = 0; i < 256; ++i) {
      auto [left, a] = expressions[random() % expressions.size()];
      auto [right, b] = expressions[random() % expressions.size()];
      bool disjunction = random() % 2;
      auto guard = disjunction ? e.plan.unite(left, right, {})
                               : e.plan.intersect(left, right, {});
      uint64_t truth = disjunction ? a | b : a & b;
      for (unsigned assignment = 0; assignment < 64; ++assignment)
        require((e.plan.intersect(guard, assignments[assignment], {}) ==
                 assignments[assignment]) ==
                    bool(truth & (uint64_t(1) << assignment)),
                "guard changed its truth table");
      expressions.emplace_back(guard, truth);
    }
    require(!e.semantics.diagnostic, "truth-table control exhausted work");
  });
  return cases.result();
}
