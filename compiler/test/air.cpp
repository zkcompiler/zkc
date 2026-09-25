#include "zkc/Relation/AIR.h"
#include "zkc/Target/Json.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <set>

using namespace llvm;
using namespace zkc::relation;
using N = AIRNode;

static unsigned checks = 0;
static void require(bool ok, StringRef message) {
  ++checks;
  if (!ok) {
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
  require(!result, "expected rejection");
  auto actual = toString(result.takeError());
  if (actual != code)
    errs() << "expected " << code << ", got " << actual << '\n';
  require(actual == code, "wrong rejection");
}
static AIRConstraint constraint(AIRScopeKind scope, std::vector<N> nodes,
                                uint32_t lookahead = 0) {
  return {{scope, lookahead}, std::move(nodes), std::nullopt, std::nullopt};
}
static AIR recurrence(StringRef field = "koala-bear") {
  // x[r+1] - x[r]^2 = 0; x[0] = public[0]; x[last] = public[1].
  auto transition = constraint(
      AIRScopeKind::Transition,
      {N::read(1, 0), N::read(0, 0), N::mul(1, 1), N::neg(2), N::add(0, 3)}, 1);
  auto first =
      constraint(AIRScopeKind::First,
                 {N::read(0, 0), N::publicInput(0), N::neg(1), N::add(0, 2)});
  auto last = constraint(AIRScopeKind::Last, {N::read(0, 0), N::publicInput(1),
                                              N::neg(1), N::add(0, 2)});
  return value(AIR::create(field.str(), 8, 2, {transition, first, last}));
}
static AIRTrace trace(StringRef field = "koala-bear") {
  AIRTrace result{{field.str(), 4, 8}, std::vector<std::string>(32, "19")};
  for (unsigned r = 0; r < 4; ++r)
    result.cells[r * 8] = std::to_string(1u << (1u << r));
  return result;
}

int main() {
  for (auto field : {"koala-bear", "bls12-381.fr", "ristretto255.scalar"}) {
    auto air = recurrence(field);
    auto t = trace(field);
    auto plan = value(air.compile(4));
    require(air.facts()[0].degree == 2 && air.facts()[0].maxOffset == 1 &&
                air.facts()[0].reads == std::vector<AIRCell>{{0, 0}, {1, 0}},
            "derived quadratic read/degree analysis");
    require(plan.cells().size() == 4 && plan.invocations().size() == 5,
            "selective schedule dimensions");
    std::set<AIRCell> seen;
    auto result = value(plan.evaluate(
        t.layout, {"2", "256"}, [&](AIRCell cell) -> Expected<std::string> {
          require(cell.column == 0 && cell.row < 4 && seen.insert(cell).second,
                  "callback only sees used cells exactly once");
          return t.cells[cell.row * 8 + cell.column];
        }));
    require(result.satisfied && result.scheduledReads == 4 &&
                result.residuals.size() == 5,
            "quadratic relation and boundaries");
    require(value(air.evaluate(t, {"2", "256"})).satisfied, "dense evaluation");
    t.cells[8] = "5";
    require(!value(plan.evaluate(t, {"2", "256"})).satisfied,
            "quadratic violation");
    t = trace(field);
    require(!value(plan.evaluate(t, {"3", "256"})).satisfied,
            "first boundary violation");
    require(!value(plan.evaluate(t, {"2", "255"})).satisfied,
            "last boundary violation");
    require(!value(plan.evaluate(t, {"256", "2"})).satisfied,
            "ordered public binding");
    t.cells[1] = "123";
    require(value(plan.evaluate(t, {"2", "256"})).satisfied,
            "unused values irrelevant");
    t.cells[1] = "01";
    refuses(plan.evaluate(t, {"2", "256"}), "relation-coefficient");
    require(value(plan.evaluate(t.layout, {"2", "256"},
                                [&](AIRCell cell) -> Expected<std::string> {
                                  return t.cells[cell.row * 8];
                                }))
                .satisfied,
            "callback contract validates only selected field values");
    t = trace(field);
    t.layout.columns = 7;
    refuses(plan.evaluate(t, {"2", "256"}), "air-trace-layout");
    t = trace(field);
    t.layout.height = 3;
    refuses(plan.evaluate(t, {"2", "256"}), "air-trace-layout");
    t = trace(field);
    t.cells.pop_back();
    refuses(plan.evaluate(t, {"2", "256"}), "air-trace-layout");
    t = trace(field);
    refuses(plan.evaluate(t, {"2"}), "air-public-shape");
    refuses(plan.evaluate(t, {"02", "256"}), "relation-coefficient");
    t.layout.field = "other";
    refuses(plan.evaluate(t, {"2", "256"}), "air-trace-field");
    auto encoded = zkc::printJson(air.encode());
    require(zkc::printJson(value(readAIRText(encoded)).encode()) == encoded,
            "normalized codec roundtrip");
  }
  auto air = recurrence();
  auto plan = value(air.compile(4));
  auto layout = trace().layout;
  refuses(plan.evaluate(layout, {"2", "256"},
                        [](AIRCell) -> Expected<std::string> {
                          return zkc::error("test-reader-error");
                        }),
          "test-reader-error");
  refuses(plan.evaluate(layout, {"2", "256"},
                        [](AIRCell) -> Expected<std::string> {
                          return std::string("2130706433");
                        }),
          "relation-coefficient");
  refuses(air.compile(0), "air-height");
  refuses(air.compile(AIRLimits::height + 1), "air-height");

  auto make = [](AIRConstraint c) {
    return AIR::create("koala-bear", 1, 0, {std::move(c)});
  };
  for (auto scope :
       {AIRScopeKind::Every, AIRScopeKind::First, AIRScopeKind::Last}) {
    auto window = value(make(constraint(scope, {N::read(4, 0)})));
    refuses(window.compile(4), "air-window-out-of-range");
  }
  auto lastWindow =
      value(make(constraint(AIRScopeKind::Last, {N::read(1, 0)})));
  refuses(lastWindow.compile(4), "air-window-out-of-range");
  refuses(make(constraint(AIRScopeKind::Transition, {N::read(2, 0)}, 1)),
          "air-window-declaration");
  auto longTransition =
      value(make(constraint(AIRScopeKind::Transition, {N::read(2, 0)}, 2)));
  require(value(longTransition.compile(4)).invocations().size() == 2,
          "offset-two scope");
  require(value(longTransition.evaluate({{"koala-bear", 1, 1}, {"9"}}, {}))
              .satisfied,
          "transition vacuity matches Lean when no row is active");
  auto extraLookahead =
      value(make(constraint(AIRScopeKind::Transition, {N::read(0, 0)}, 3)));
  require(value(extraLookahead.compile(4)).invocations().size() == 1,
          "explicit lookahead independent of actual offset");
  auto repeated =
      value(make(constraint(AIRScopeKind::Every, {N::read(0, 0), N::read(0, 0),
                                                  N::neg(1), N::add(0, 2)})));
  auto repeatedPlan = value(repeated.compile(4));
  require(repeated.facts()[0].reads.size() == 1 &&
              repeated.facts()[0].readNodes == 2 &&
              repeatedPlan.cells().size() == 4 &&
              repeatedPlan.invocations()[0].slots ==
                  std::vector<uint32_t>{0, 0},
          "distinct read nodes share one slot");
  auto transitionZero =
      value(make(constraint(AIRScopeKind::Transition, {N::read(0, 0)}, 0)));
  require(value(transitionZero.compile(4)).invocations().size() == 4,
          "transition zero equals every");

  auto c = constraint(AIRScopeKind::Every,
                      {N::read(0, 0), N::mul(0, 0), N::mul(1, 1)});
  c.declaredDegree = 3;
  refuses(make(c), "air-degree-declaration");
  c.declaredDegree = 7;
  require(value(make(c)).facts()[0].degree == 4,
          "degree is computed not copied from declaration");
  c.declaredMaxOffset = AIRLimits::offset + 1;
  refuses(make(c), "air-declaration-limit");
  c = constraint(AIRScopeKind::Transition, {N::read(1, 0)}, 1);
  c.declaredMaxOffset = 0;
  refuses(make(c), "air-window-declaration");
  c.declaredMaxOffset = 7;
  require(value(make(c)).facts()[0].maxOffset == 1,
          "window derived not provider claim");

  auto zero = value(make(constraint(AIRScopeKind::Every, {N::constant("0")})));
  auto zeroPlan = value(zero.compile(3));
  require(zeroPlan.cells().empty() && zero.facts()[0].degree == 0,
          "constant no reads");
  require(value(zeroPlan.evaluate({{"koala-bear", 3, 1}, {"0", "0", "0"}}, {}))
              .satisfied,
          "zero-valued trace accepted");
  auto nonzero =
      value(make(constraint(AIRScopeKind::Every, {N::constant("1")})));
  require(!value(nonzero.evaluate({{"koala-bear", 1, 1}, {"0"}}, {})).satisfied,
          "nonzero constant violates");
  auto both =
      value(AIR::create("koala-bear", 0, 0,
                        {constraint(AIRScopeKind::First, {N::constant("0")}),
                         constraint(AIRScopeKind::Last, {N::constant("0")})}));
  require(value(both.compile(1)).invocations().size() == 2 &&
              value(both.evaluate({{"koala-bear", 1, 0}, {}}, {})).satisfied,
          "single row both boundaries and zero columns");
  auto empty = value(AIR::create("koala-bear", 1, 0, {}));
  require(value(empty.evaluate({{"koala-bear", 1, 1}, {"0"}}, {})).satisfied,
          "empty constraint list");

  refuses(AIR::create("unknown", 1, 0, {}), "air-field");
  refuses(AIR::create("koala-bear", AIRLimits::columns + 1, 0, {}),
          "air-dimension-limit");
  refuses(AIR::create("koala-bear", 1, AIRLimits::publicInputs + 1, {}),
          "air-dimension-limit");
  refuses(AIR::create("koala-bear", 1, 0,
                      std::vector<AIRConstraint>(AIRLimits::constraints + 1)),
          "air-constraint-limit");
  refuses(make(constraint(AIRScopeKind::Every, {})), "air-expression");
  refuses(make(constraint(AIRScopeKind::Every, {N::read(0, 1)})), "air-column");
  refuses(make(constraint(AIRScopeKind::Every, {N::publicInput(0)})),
          "air-public-index");
  refuses(make(constraint(AIRScopeKind::Every,
                          {N::read(AIRLimits::offset + 1, 0)})),
          "air-offset-limit");
  refuses(make(constraint(AIRScopeKind::Transition, {N::constant("0")},
                          AIRLimits::offset + 1)),
          "air-offset-limit");
  refuses(make(constraint(AIRScopeKind::Every, {N::constant("0")}, 1)),
          "air-scope");
  refuses(make(constraint(static_cast<AIRScopeKind>(99), {N::constant("0")})),
          "air-scope");
  refuses(make(constraint(AIRScopeKind::Every, {N::add(0, 0)})),
          "air-node-reference");
  refuses(make(constraint(AIRScopeKind::Every,
                          {N::constant("0"), N::constant("0")})),
          "air-dead-node");
  for (auto scalar : {"", "01", "-1", "2130706433", "1e2"})
    refuses(make(constraint(AIRScopeKind::Every, {N::constant(scalar)})),
            "relation-coefficient");
  auto malformed = N::constant("0");
  malformed.column = 1;
  refuses(make(constraint(AIRScopeKind::Every, {malformed})), "air-node-shape");
  malformed = N::constant("0");
  malformed.kind = static_cast<AIRKind>(99);
  refuses(make(constraint(AIRScopeKind::Every, {malformed})),
          "air-unsupported-operation");
  std::vector<N> deep{N::constant("0")};
  for (unsigned i = 1; i <= AIRLimits::depth; ++i)
    deep.push_back(N::neg(i - 1));
  refuses(make(constraint(AIRScopeKind::Every, deep)), "air-depth-limit");
  deep.pop_back();
  require(value(make(constraint(AIRScopeKind::Every, deep))).facts()[0].depth ==
              AIRLimits::depth,
          "maximum admitted depth");
  std::vector<N> degree{N::read(0, 0)};
  for (unsigned i = 1; i <= 21; ++i)
    degree.push_back(N::mul(i - 1, i - 1));
  refuses(make(constraint(AIRScopeKind::Every, degree)), "air-degree-limit");
  refuses(make(constraint(AIRScopeKind::Every,
                          std::vector<N>(AIRLimits::nodes + 1))),
          "air-node-limit");
  std::vector<AIRConstraint> expensive(
      65, constraint(AIRScopeKind::Every, {N::constant("0")}));
  auto work = value(AIR::create("koala-bear", 1, 0, expensive));
  refuses(work.compile(AIRLimits::height), "air-work-limit");
  AIRTrace tooBig{{"koala-bear", 65536, 17}, {}};
  auto wide = value(AIR::create("koala-bear", 17, 0, {}));
  refuses(value(wide.compile(65536)).evaluate(tooBig, {}), "air-cell-limit");
  std::vector<N> wideReads{N::read(0, 0)};
  for (uint32_t col = 1; col < 17; ++col) {
    uint32_t previous = wideReads.size() - 1;
    wideReads.push_back(N::read(0, col));
    wideReads.push_back(N::add(previous, previous + 1));
  }
  auto tooManyCells = value(AIR::create(
      "koala-bear", 17, 0, {constraint(AIRScopeKind::Every, wideReads)}));
  refuses(tooManyCells.compile(65536), "air-cell-limit");

  // JSON ambiguity, unsupported syntax, and pre-parser resource controls.
  refuses(readAIRText("{"), "air-invalid-json");
  refuses(readAIRText("{}"), "air-json-shape");
  refuses(readAIRText("{\"schema\":\"x\",\"schema\":\"y\"}"),
          "air-duplicate-key");
  refuses(readAIRText("{\"schema\":\"x\",\"sch\\u0065ma\":\"y\"}"),
          "air-duplicate-key");
  refuses(readAIRText("{\"x\":1e2}"), "air-invalid-json");
  refuses(readAIRText("{\"x\":1.0}"), "air-invalid-json");
  refuses(readAIRText("{\"x\":000}"), "air-invalid-json");
  refuses(readAIRText("{\"x\":12345678901}"), "air-invalid-json");
  refuses(readAIRText("{\"x\":-0}"), "air-invalid-json");
  refuses(readAIRText("\"\\ud800\""), "air-invalid-json");
  refuses(readAIRText(std::string(AIRLimits::bytes + 1, ' ')),
          "air-byte-limit");
  refuses(readAIRText(std::string(17, '[') + std::string(17, ']')),
          "air-json-depth-limit");
  refuses(readAIRText("\"" + std::string(257, 'a') + "\""), "air-string-limit");
  auto encoded = air.encode();
  (*encoded.getAsObject())["lookup"] = true;
  refuses(readAIR(encoded), "air-json-shape");
  encoded = air.encode();
  auto *nodes = encoded.getAsObject()
                    ->getArray("constraints")
                    ->front()
                    .getAsObject()
                    ->getArray("nodes");
  (*nodes)[0] = json::Object{{"op", "lookup"}};
  refuses(readAIR(encoded), "air-unsupported-operation");
  encoded = air.encode();
  (*encoded.getAsObject())["columns"] = -1;
  refuses(readAIR(encoded), "air-json-shape");
  json::Value traceJson = json::Object{{"field", "koala-bear"},
                                       {"height", 1},
                                       {"columns", 1},
                                       {"cells", json::Array{"0"}}};
  require(value(readAIRTrace(traceJson)).cells == std::vector<std::string>{"0"},
          "trace codec");
  (*traceJson.getAsObject())["height"] = 0;
  refuses(readAIRTrace(traceJson), "air-height");
  (*traceJson.getAsObject())["height"] = 65536;
  (*traceJson.getAsObject())["columns"] = 65536;
  refuses(readAIRTrace(traceJson), "air-cell-limit");
  outs() << "AIR controls passed: " << checks << " checks\n";
}
