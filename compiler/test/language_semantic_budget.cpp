#include "../lib/Language/Semantics.h"
#include "support/NativeCases.h"

using namespace llvm;
using namespace zkc::language;
using namespace zkc::language::detail;
using namespace zkc::test;
namespace {
constexpr Span callerSpan{{3}, 17, 29};
Type natural(uint64_t value) {
  Type result(Type::Kind::Natural);
  result.dimension = Natural::constant(value);
  return result;
}
void diagnostic(Semantics &types, StringRef code) {
  require(types.diagnostic.has_value(), "missing semantic diagnostic");
  const auto &error = *types.diagnostic;
  require(error.code == code, "unexpected diagnostic: " + error.code);
  require(error.primary &&
              error.primary->source.index == callerSpan.source.index &&
              error.primary->begin == callerSpan.begin &&
              error.primary->end == callerSpan.end,
          "adapter lost its caller span");
}
} // namespace
int main() {
  Cases cases;
  cases.run("normalization admits every unit before overflow", [] {
    Limits limits;
    const std::vector<Declaration> declarations;
    NaturalArithmetic algebra;
    Type input(Type::Kind::Natural);
    input.dimension = take(algebra.powerOfTwo(take(Natural::atom("N"))));
    input.symbolic = true;
    for (uint64_t allowance : {uint64_t(100), uint64_t(10)}) {
      uint64_t remaining = allowance;
      Work work{limits};
      work.allowance = &remaining;
      Semantics types(declarations, {}, work);
      require(!types.substitute(input, {{"N", natural(64)}}, callerSpan),
              "overflowing substitution succeeded");
      diagnostic(types, allowance == 100 ? "source.natural" : "source.limit");
      auto arithmeticWork = limits.work - types.naturals.remainingWork();
      require(arithmeticWork == (allowance == 100 ? 4 : 2),
              "normalization ran beyond admission or lost performed units");
      require(work.used == 7 + arithmeticWork &&
                  remaining == allowance - work.used,
              "normalization was omitted or double charged");
    }
  });
  cases.run("placement remapping retains failed validation prefixes", [] {
    Limits limits;
    const std::vector<Declaration> declarations;
    uint64_t remaining = 100;
    Work work{limits};
    work.allowance = &remaining;
    Semantics types(declarations, {}, work);
    require(!types.remapPlacement(DataPlacement{{0, 1}}, {0, 0}, 2, callerSpan),
            "duplicate role map succeeded");
    diagnostic(types, "source.roles");
    require(remaining == 97 && work.used == 3,
            "failed remap discarded validation work");
    types.diagnostic.reset();
    remaining = 4;
    require(!types.remapPlacement(DataPlacement{{0, 1}}, {1, 0}, 2, callerSpan),
            "remap ignored enclosing remaining");
    diagnostic(types, "source.limit");
    require(remaining == 0 && work.used == 7,
            "bounded remap discarded its admitted prefix");
  });
  cases.run("successful remapping spends exactly eleven units", [] {
    Limits limits;
    const std::vector<Declaration> declarations;
    uint64_t remaining = 11;
    Work work{limits};
    work.allowance = &remaining;
    Semantics types(declarations, {}, work);
    auto result =
        types.remapPlacement(DataPlacement{{0, 1}}, {1, 0}, 2, callerSpan);
    require(result && *result == ValuePlacement(DataPlacement{{0, 1}}),
            "valid remap changed canonical roles");
    require(remaining == 0 && work.used == 11,
            "remap successful accounting changed");
  });
  cases.run("normalization and remapping preserve cancellation", [] {
    Limits limits;
    const std::vector<Declaration> declarations;
    uint64_t remaining = 100;
    Work work{limits};
    work.allowance = &remaining;
    work.cancellation.emplace();
    Semantics types(declarations, {}, work);
    take(types.naturals.add(Natural::constant(1), Natural::constant(1)));
    require(work.used == 2 && remaining == 98,
            "normalization did not debit Work directly");
    work.cancellation->cancel();
    auto cancelled = types.naturals.add(Natural::constant(1), Natural{});
    require(!cancelled, "cancelled normalization succeeded");
    types.accept(cancelled.takeError(), callerSpan);
    diagnostic(types, "source.cancelled");
    types.diagnostic.reset();
    require(!types.remapPlacement(DataPlacement{{0}}, {0}, 1, callerSpan),
            "cancelled remapping succeeded");
    diagnostic(types, "source.cancelled");
    require(work.used == 2 && remaining == 98,
            "cancellation changed already admitted spending");
  });
  cases.run("additive cancellation shares semantic admission", [] {
    Limits limits;
    const std::vector<Declaration> declarations;
    Declaration caller;
    NaturalArithmetic algebra;
    auto n = take(Natural::atom("N"));
    auto bound = take(algebra.add(n, Natural::constant(1)));
    uint64_t cost = 0;
    for (unsigned trial = 0; trial < 3; ++trial) {
      uint64_t allowance = trial == 0 ? limits.work : cost - (trial == 2);
      uint64_t remaining = allowance;
      Work work{limits};
      work.allowance = &remaining;
      Semantics types(declarations, {}, work);
      bool result =
          types.assumptions(caller, {bound, bound, callerSpan}, {}, callerSpan);
      if (trial == 0) {
        require(result, "valid additive cancellation refused");
        cost = work.used;
      } else if (trial == 1) {
        require(result && remaining == 0,
                "successful additive cancellation was not exact");
      } else {
        require(!result, "additive cancellation ignored shared allowance");
        diagnostic(types, "source.limit");
        require(work.used > 0, "failed additive cancellation refunded work");
      }
    }
  });
  cases.run("relation data snapshots respect the enclosing allowance", [] {
    Limits limits;
    const std::vector<Declaration> declarations;
    Declaration scope;
    for (uint64_t allowance : {uint64_t(2), uint64_t(1)}) {
      uint64_t remaining = allowance;
      Work work{limits};
      work.allowance = &remaining;
      Semantics types(declarations, {}, work);
      bool result = types.relationData(scope, Type{}, callerSpan, 1);
      require(result == (allowance == 2), "relation admission changed");
      require(remaining == 0 && work.used == allowance,
              "relation parsing lost admitted work");
      if (!result)
        diagnostic(types, "source.limit");
    }
  });
  cases.run("nested port observation reconciles both results and failures", [] {
    Limits limits;
    const std::vector<Declaration> declarations;
    Port port;
    port.type = Type{};
    port.roles = {0};
    uint64_t cost = 0;
    for (unsigned trial = 0; trial < 3; ++trial) {
      uint64_t allowance = trial == 0 ? limits.work : cost - (trial == 2);
      uint64_t remaining = allowance;
      Work work{limits};
      work.allowance = &remaining;
      Semantics types(declarations, {}, work);
      auto observed = types.nativePortLayout(port);
      if (trial < 2) {
        require(take(std::move(observed)).leaves.size() == 1,
                "port observation changed");
        if (trial == 0) {
          cost = work.used;
          require(cost > 1, "port observation bypassed enclosing work");
        } else
          require(remaining == 0, "port observation was not exact");
      } else {
        refuses(std::move(observed), "source.limit");
        require(work.used > 0 && work.used <= allowance,
                "failed port observation lost bounded partial work");
      }
    }
  });
  return cases.result();
}
