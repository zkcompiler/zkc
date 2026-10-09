#include "zkc/Relation/AIR.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace zkc::relation;
using N = AIRNode;
static constexpr uint64_t modulus = 2130706433;

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
struct ScalarAlgebra {
  const AIRExpressionView &view;
  const AIRTrace &trace;
  ArrayRef<std::string> publics;
  uint32_t row;
  Expected<uint64_t> input(uint32_t index, StringRef) {
    const auto &binding = view.inputs[index];
    if (binding.kind == AIRExpressionInput::Kind::Public)
      return std::stoull(publics[binding.publicIndex]);
    auto actualRow = row + binding.cell.row;
    if (actualRow >= trace.layout.height)
      return zkc::error("test-window");
    return std::stoull(
        trace.cells[actualRow * trace.layout.columns + binding.cell.column]);
  }
  Expected<uint64_t> constant(StringRef, StringRef text) {
    return std::stoull(text.str());
  }
  Expected<uint64_t> add(StringRef, uint64_t a, uint64_t b) {
    return (a + b) % modulus;
  }
  Expected<uint64_t> mul(StringRef, uint64_t a, uint64_t b) {
    return a * b % modulus;
  }
  Expected<uint64_t> neg(StringRef, uint64_t a) {
    return (modulus - a) % modulus;
  }
  Expected<uint64_t> embed(StringRef, StringRef, uint64_t) {
    return zkc::error("test-no-embedding");
  }
};

int main() {
  auto air = value(AIR::create(
      "koala-bear", 1, 2,
      {{{AIRScopeKind::Transition, 1},
        {N::read(1, 0), N::read(0, 0), N::mul(1, 1), N::neg(2), N::add(0, 3)},
        {},
        {}},
       {{AIRScopeKind::First, 0},
        {N::read(0, 0), N::publicInput(0), N::neg(1), N::add(0, 2)},
        {},
        {}},
       {{AIRScopeKind::Last, 0},
        {N::read(0, 0), N::publicInput(1), N::neg(1), N::add(0, 2)},
        {},
        {}}}));
  AIRTrace trace{{"koala-bear", 4, 1}, {"2", "4", "16", "256"}};
  std::vector<std::string> publics{"2", "256"};
  std::vector<AIRExpressionView> views;
  for (uint32_t c = 0; c < air.constraints().size(); ++c) {
    auto view = value(air.expressionView(c));
    std::vector<uint32_t> weights;
    for (const auto &input : view.inputs)
      weights.push_back(input.kind == AIRExpressionInput::Kind::Read ? 1 : 0);
    require(value(view.expression.degrees(weights)).back() ==
                air.facts()[c].degree,
            "public constants preserve finite-AIR degree");
    views.push_back(std::move(view));
  }
  require(views[0].inputs.size() == 2 &&
              views[0].inputs[0].cell == AIRCell{1, 0} &&
              views[0].inputs[1].cell == AIRCell{0, 0},
          "exact relative-read map");
  for (unsigned mutation = 0; mutation < 6; ++mutation) {
    auto changed = trace;
    auto statement = publics;
    if (mutation < 4)
      changed.cells[mutation] =
          std::to_string(std::stoull(changed.cells[mutation]) + 1);
    if (mutation == 4)
      statement[1] = "255";
    auto result = value(air.evaluate(changed, statement));
    require(result.satisfied == (mutation == 5), "adversarial AIR fixture");
    for (const auto &residual : result.residuals) {
      ScalarAlgebra algebra{views[residual.constraint], changed, statement,
                            residual.row};
      auto output =
          value(views[residual.constraint].expression.evaluate<uint64_t>(
              {0}, algebra));
      require(output.size() == 1 && std::to_string(output[0]) == residual.value,
              "shared arena agrees with independent finite AIR evaluator");
    }
  }
  auto missing = air.expressionView(3);
  require(!missing && toString(missing.takeError()) == "air-constraint-index",
          "unknown constraint refuses");
  auto cancel = value(AIR::create("koala-bear", 1, 0,
                                  {{{AIRScopeKind::Last, 0},
                                    {N::read(1, 0), N::neg(0), N::add(0, 1)},
                                    {},
                                    {}}}));
  (void)value(cancel.expressionView(0));
  auto plan = cancel.compile(4);
  require(!plan && toString(plan.takeError()) == "air-window-out-of-range",
          "algebraic cancellation does not erase illegal AIR reads");
  std::vector<N> highPublic{N::publicInput(0)};
  for (uint32_t i = 0; i < 40; ++i)
    highPublic.push_back(N::mul(i, i));
  highPublic.push_back(N::read(0, 0));
  highPublic.push_back(N::mul(40, 41));
  auto high = value(
      AIR::create("koala-bear", 1, 1,
                  {{{AIRScopeKind::Every, 0}, std::move(highPublic), {}, {}}}));
  auto highView = value(high.expressionView(0));
  require(high.facts()[0].degree == 1 &&
              value(highView.expression.degrees({0, 1})).back() == 1,
          "large powers of public constants preserve the AIR degree");
  auto nonconstant = highView.expression.degrees({1, 1});
  require(!nonconstant && toString(nonconstant.takeError()) == "ring-degree",
          "the selected polynomial substitution enforces its degree limit");
  outs() << "finite AIR and shared ring interpretation agree\n";
}
