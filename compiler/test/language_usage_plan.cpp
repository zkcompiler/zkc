#include "../lib/Language/UsagePlan.h"
#include "support/NativeCases.h"
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
  return cases.result();
}
