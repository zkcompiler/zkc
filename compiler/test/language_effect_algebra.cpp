#include "../lib/Language/Effects.h"
#include "support/NativeCases.h"
#include <array>
using namespace zkc::language;
using namespace zkc::language::detail;
using namespace zkc::test;
namespace {
Effects bits(unsigned value) { return {bool(value & 1), bool(value & 2)}; }
EffectSummary formula(unsigned code) {
  EffectSummary result{bits(code & 3)};
  for (unsigned slot = 0; slot < 3; ++slot) {
    auto mask = (code >> (2 * (slot + 1))) & 3;
    if (mask)
      result.dependencies.emplace(slot, bits(mask));
  }
  return result;
}
unsigned evaluate(const EffectSummary &summary, unsigned valuation) {
  unsigned result =
      unsigned(summary.fixed.mayStop) | (unsigned(summary.fixed.opaque) << 1);
  for (const auto &[slot, mask] : summary.dependencies) {
    unsigned allowed = unsigned(mask.mayStop) | (unsigned(mask.opaque) << 1);
    result |= ((valuation >> (2 * slot)) & 3) & allowed;
  }
  return result;
}
} // namespace
int main() {
  Cases cases;
  cases.run("effect containment agrees with every concrete valuation", [] {
    Limits limits;
    Work work{limits};
    std::vector<Declaration> declarations;
    Semantics types(declarations, {}, work);
    std::array<EffectSummary, 256> formulas;
    for (unsigned code = 0; code < formulas.size(); ++code)
      formulas[code] = formula(code);
    for (const auto &left : formulas)
      for (const auto &right : formulas) {
        bool expected = true;
        for (unsigned valuation = 0; valuation < 64; ++valuation)
          expected &=
              (evaluate(left, valuation) & ~evaluate(right, valuation)) == 0;
        require(effectsWithin(types, left, right) == expected,
                "symbolic containment differs from concrete valuations");
        require(!types.diagnostic, "unexpected work refusal");
      }
  });
  cases.run("effect union and substitution preserve interpretation", [] {
    Limits limits;
    Work work{limits};
    std::vector<Declaration> declarations;
    Semantics types(declarations, {}, work);
    const std::array<EffectSummary, 3> arguments = {formula(12), formula(48),
                                                    formula(192)};
    for (unsigned code = 0; code < 256; ++code) {
      auto original = formula(code);
      auto substituted = substituteEffects(types, original, arguments);
      require(bool(substituted), "valid substitution refused");
      auto joined = original;
      require(joinEffects(types, joined, formula(37)), "valid union refused");
      for (unsigned valuation = 0; valuation < 64; ++valuation) {
        unsigned actuals = 0;
        for (unsigned slot = 0; slot < arguments.size(); ++slot)
          actuals |= evaluate(arguments[slot], valuation) << (2 * slot);
        require(evaluate(*substituted, valuation) ==
                    evaluate(original, actuals),
                "substitution changed the effect interpretation");
        require(evaluate(joined, valuation) ==
                    (evaluate(original, valuation) |
                     evaluate(formula(37), valuation)),
                "union changed the effect interpretation");
      }
    }
  });
  cases.run("effect work limit and invalid substitution refuse", [] {
    Limits limits;
    limits.work = 0;
    Work exhausted{limits};
    std::vector<Declaration> declarations;
    Semantics bounded(declarations, {}, exhausted);
    require(!effectsWithin(bounded, formula(0), formula(0)) &&
                bounded.diagnostic &&
                bounded.diagnostic->code == "source.limit",
            "empty effect comparison bypassed work accounting");
    Limits normal;
    Work work{normal};
    Semantics types(declarations, {}, work);
    require(!substituteEffects(types, formula(4), {}),
            "missing callback substitution accepted");
    require(types.diagnostic && types.diagnostic->code == "source.effect",
            "missing callback produced no diagnostic");
  });
  cases.run("abstract Math calls retain their total effect contract", [] {
    auto captured = take(capture({{"m", R"(module m;
domain F=field("koala-bear");
interface I {math fn apply(x:F)->F;}
fn relay<C:I>(x:F)->F effects(){return C::apply(x);}
)",
                                   "abstract-math.zkc"}}));
    take(analyze(captured).checkedProject());
  });
  cases.run(
      "authored callback ceilings resist coordinated summary mutation", [] {
        auto captured = take(capture({{"m", R"(module m;
domain F=field("koala-bear");
fn run(x:F,body:fn(F)->F effects(stop))->F effects(body){return body(x);}
)",
                                       "effect-evidence.zkc"}}));
        auto project = take(analyze(captured).checkedProject());
        for (const auto &decl : project.declarations())
          if (decl.qualifiedName == "m::run") {
            auto &changed = const_cast<Declaration &>(decl);
            changed.scopedInputs.front().signature.allowance = {};
            changed.effectAllowance = EffectSummary{};
            auto body = std::make_shared<Body>(*changed.body);
            body->scopedBindings.front().signature.allowance = {};
            body->effects = {};
            changed.body = body;
          }
        auto error = checkScopedElaboration(project);
        require(bool(error),
                "coordinated callback ceiling and summary mutation accepted");
        llvm::consumeError(std::move(error));
      });
  for (bool abstract : {false, true})
    cases.run(
        abstract ? "abstract effect source survives contract mutation"
                 : "defined effect source survives contract mutation",
        [&] {
          const std::string source =
              abstract
                  ? "interface I{fn work(x:F)->F effects(stop);}"
                  : "fn work(x:F)->F effects(stop){require x==1;return x;}";
          auto captured = take(capture(
              {{"m", "module m;domain F=field(\"koala-bear\");" + source,
                "contract-source.zkc"}}));
          auto project = take(analyze(captured).checkedProject());
          bool mutated = false;
          for (const auto &decl : project.declarations())
            if (decl.name == "work") {
              const_cast<Declaration &>(decl).effectAllowance = EffectSummary{};
              mutated = true;
            }
          require(mutated, "missing contract fixture");
          auto error = checkScopedElaboration(project);
          require(bool(error), "altered authored output contract accepted");
          require(
              llvm::toString(std::move(error)).find("source.scoped-witness") !=
                  std::string::npos,
              "wrong contract witness diagnostic");
        });
  return cases.result();
}
