#include "support/NativeCases.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Program/ResourceOrigins.h"

using namespace llvm;
using namespace zkc;
using namespace zkc::program;
using namespace zkc::test;
namespace {
const std::string resource = "resource_unit:Guard";
const std::string transcript = "transcript:merlin3.bls12-381.fr64be/0";
using Roots = std::map<unsigned, unsigned>;

Function identityFunction(std::string name = "identity") {
  return {name,
          {{"state", resource}},
          {resource},
          {{"", Return{{"state"}}}},
          LogicalOrigin{name, {}}};
}
LocalDefinitions fixture() {
  return {{{"create", {"resource_unit.create", {"Guard"}, ""}},
           {"pass", {"resource_unit.pass", {"Guard"}, ""}}},
          {identityFunction()}};
}
ResourceOriginSummary query(const LocalDefinitions &definitions,
                            StringRef function = "identity",
                            ArrayRef<protocol::LocalRealization> finite = {}) {
  uint64_t work = 100000;
  return take(analyzeResourceOrigins(definitions, finite, function, work));
}
void expect(const ResourceOriginSummary &summary, Roots roots,
            bool continues = true) {
  require(summary.continues == continues && summary.roots == roots,
          "unexpected resource roots or continuation");
}
void refuse(Error result, StringRef code) {
  require(bool(result), "expected refusal: " + code);
  const auto message = toString(std::move(result));
  require(namesIdentifier(message, code), "unexpected refusal: " + message);
}
LocalDefinitions conditional() {
  auto model = fixture();
  auto &fn = model.functions[0];
  fn.arguments.push_back({"condition", "bool"});
  fn.body = {{"choose", Conditional{"condition",
                                    {"state"},
                                    {{"", Yield{{"state"}}}},
                                    {{"", Yield{{"state"}}}},
                                    {"result"}}},
             {"", Return{{"result"}}}};
  return model;
}
LocalDefinitions loop() {
  auto model = fixture();
  auto &fn = model.functions[0];
  fn.arguments.push_back({"lower", "index"});
  fn.arguments.push_back({"upper", "index"});
  fn.body = {{"iterate", For{"i",
                             "lower",
                             "upper",
                             {{"s", "state"}},
                             {},
                             {{"", Yield{{"s"}}}},
                             {"result"}}},
             {"", Return{{"result"}}}};
  return model;
}
protocol::LocalRealization fold(unsigned states = 1) {
  protocol::LocalRealization result;
  result.name = "fold";
  result.inputs = {"index"};
  result.inputs.insert(result.inputs.end(), states, resource);
  result.outputs.assign(states, resource);
  result.kind = protocol::LocalRealization::Kind::FiniteFold;
  result.domainArguments = 1;
  result.callbacks = {"identity"};
  return result;
}
} // namespace

int main() {
  Cases cases;
  cases.run("identity retains its exact formal resource",
            [&] { expect(query(fixture()), {{0, 0}}); });
  cases.run("fresh resource is not the unused formal", [&] {
    auto model = fixture();
    model.functions[0].body = {
        {"fresh", Operation{"create", {}, {}, {"fresh"}}},
        {"", Return{{"fresh"}}}};
    expect(query(model), {});
  });
  cases.run("matching types alone grant no successor law", [&] {
    auto model = fixture();
    model.functions[0].body = {
        {"pass", Operation{"pass", {}, {"state"}, {"next"}}},
        {"", Return{{"next"}}}};
    expect(query(model), {});
  });
  cases.run("history facet preserves a changed transcript", [&] {
    auto fn = identityFunction();
    fn.arguments = {{"state", transcript}, {"label", "bytes"}};
    fn.results = {transcript};
    fn.body = {
        {"draw", Operation{"draw", {}, {"state", "label"}, {"next", "sample"}}},
        {"", Return{{"next"}}}};
    LocalDefinitions model{
        {{"draw",
          {"transcript.challenge", {"merlin3.bls12-381.fr64be/0"}, ""}}},
        {fn}};
    expect(query(model), {{0, 0}});
  });
  cases.run("sampling facet preserves nonzero result position", [&] {
    auto fn = identityFunction();
    fn.arguments = {{"state", "rng:bls12-381.fr"}};
    fn.results = {"field:bls12-381.fr", "rng:bls12-381.fr"};
    fn.body = {{"draw", Operation{"draw", {}, {"state"}, {"sample", "next"}}},
               {"", Return{{"sample", "next"}}}};
    LocalDefinitions model{{{"draw", {"random.draw", {"bls12-381.fr"}, ""}}},
                           {fn}};
    expect(query(model), {{1, 0}});
  });
  cases.run("copyable formals never become resource facts", [&] {
    auto model = fixture();
    model.functions[0].arguments[0].type = "bool";
    model.functions[0].results = {"bool"};
    expect(query(model), {});
  });
  cases.run("conditional continuing arms must agree", [&] {
    auto model = conditional();
    expect(query(model), {{0, 0}});
    model.functions[0].body[0].get<Conditional>()->elseBody = {
        {"fresh", Operation{"create", {}, {}, {"fresh"}}},
        {"", Yield{{"fresh"}}}};
    expect(query(model), {});
  });
  cases.run("stopped conditional arm is not an unknown returning arm", [&] {
    auto model = conditional();
    model.functions[0].body[0].get<Conditional>()->elseBody = {
        {"stop", Stop{"reject"}}};
    expect(query(model), {{0, 0}});
  });
  cases.run("both stopped arms leave no successful result", [&] {
    auto model = conditional();
    auto &branch = *model.functions[0].body[0].get<Conditional>();
    branch.thenBody = {{"left", Stop{"reject"}}};
    branch.elseBody = {{"right", Stop{"reject"}}};
    branch.outputs.clear();
    model.functions[0].results.clear();
    model.functions[0].body.back().value = Return{};
    expect(query(model), {}, false);
  });
  cases.run("callee roots substitute actual argument positions", [&] {
    auto model = fixture();
    auto caller = identityFunction("caller");
    caller.arguments.push_back({"other", resource});
    caller.body = {{"call", LocalApply{"identity", {"other"}, {"next"}}},
                   {"", Return{{"next"}}}};
    model.functions.push_back(caller);
    expect(query(model, "caller"), {{0, 1}});
  });
  cases.run("stopping helper makes its caller noncontinuing", [&] {
    auto model = fixture();
    model.functions[0].body = {{"stop", Stop{"reject"}}};
    auto caller = identityFunction("caller");
    caller.body = {{"call", LocalApply{"identity", {"state"}, {"next"}}},
                   {"", Return{{"next"}}}};
    model.functions.push_back(caller);
    expect(query(model, "caller"), {}, false);
  });
  cases.run("loop invariant keeps its initial root",
            [&] { expect(query(loop()), {{0, 0}}); });
  cases.run("loop fresh replacement loses the initial root", [&] {
    auto model = loop();
    model.functions[0].body[0].get<For>()->body = {
        {"fresh", Operation{"create", {}, {}, {"fresh"}}},
        {"", Yield{{"fresh"}}}};
    expect(query(model), {});
  });
  cases.run("loop permutation cannot assume one iteration", [&] {
    auto model = loop();
    auto &fn = model.functions[0];
    fn.arguments.push_back({"other", resource});
    fn.results.push_back(resource);
    auto &iter = *fn.body[0].get<For>();
    iter.carried.push_back({"t", "other"});
    iter.outputs.push_back("otherResult");
    iter.body = {{"", Yield{{"t", "s"}}}};
    fn.body.back().value = Return{{"result", "otherResult"}};
    expect(query(model), {});
  });
  cases.run("stopping iteration retains the zero-trip initial state", [&] {
    auto model = loop();
    model.functions[0].body[0].get<For>()->body = {{"stop", Stop{"reject"}}};
    expect(query(model), {{0, 0}});
  });
  cases.run("conditional loop accounts for the leading yield predicate", [&] {
    auto model = loop();
    auto &iter = *model.functions[0].body[0].get<For>();
    iter.conditional = true;
    iter.body = {{"condition", BooleanConstant{"condition", false}},
                 {"", Yield{{"condition", "s"}}}};
    expect(query(model), {{0, 0}});
  });
  cases.run("match captures preserve roots but payloads remain unknown", [&] {
    auto model = fixture();
    auto choice =
        protocol::encodeVariant({"Choice", {{"Left", {}}, {"Right", {}}}});
    require(bool(choice), "choice fixture");
    auto &fn = model.functions[0];
    fn.arguments.push_back({"choice", *choice});
    fn.body = {{"match", Match{"choice",
                               {"state"},
                               {{"Left", {}, {{"", Yield{{"state"}}}}},
                                {"Right", {}, {{"", Yield{{"state"}}}}}},
                               {"next"}}},
               {"", Return{{"next"}}}};
    expect(query(model), {{0, 0}});
    auto payload = protocol::encodeVariant({"Payload", {{"Some", {resource}}}});
    require(bool(payload), "payload fixture");
    fn.arguments = {{"choice", *payload}};
    fn.body[0].value = Match{"choice",
                             {},
                             {{"Some", {"state"}, {{"", Yield{{"state"}}}}}},
                             {"next"}};
    expect(query(model), {});
  });
  cases.run("finite fold roots refer to initial state after domain inputs",
            [&] {
              auto model = fixture();
              auto realization = fold();
              expect(query(model, "fold", {realization}), {{0, 1}});
            });
  cases.run("unused finite fold must reject a fresh callback root", [&] {
    auto model = fixture();
    model.functions[0].body = {
        {"fresh", Operation{"create", {}, {}, {"fresh"}}},
        {"", Return{{"fresh"}}}};
    // No ordinary body calls this realization: dormant obligations still apply.
    refuse(protocol::admitNativeLocalDefinitions(model, {fold()}),
           "mathematical-formation");
  });
  cases.run("logical participants preserve dormant finite callback roots", [&] {
    auto definitions = fixture();
    Participants model;
    model.stage = Participants::Stage::Logical;
    model.bindings = definitions.bindings;
    model.functions = definitions.functions;
    require(!protocol::admit(model, {fold()}),
            "logical finite participant closure was refused");
    model.functions[0].body = {
        {"fresh", Operation{"create", {}, {}, {"fresh"}}},
        {"", Return{{"fresh"}}}};
    refuse(protocol::admit(model, {fold()}), "mathematical-formation");
    model.stage = Participants::Stage::Physical;
    refuse(protocol::admit(model, {fold()}), "local-realization-context");
  });
  cases.run("finite fold cannot exchange equal-typed state slots", [&] {
    auto model = fixture();
    model.functions[0].arguments.push_back({"other", resource});
    model.functions[0].results.push_back(resource);
    model.functions[0].body = {{"", Return{{"other", "state"}}}};
    refuse(protocol::admitNativeLocalDefinitions(model, {fold(2)}),
           "mathematical-formation");
  });
  cases.run("finite root checks follow actual helper chains", [&] {
    auto model = fixture();
    model.functions.push_back(identityFunction("step"));
    model.functions[1].body = {
        {"call", LocalApply{"identity", {"state"}, {"next"}}},
        {"", Return{{"next"}}}};
    auto realization = fold();
    realization.callbacks = {"step"};
    expect(query(model, "fold", {realization}), {{0, 1}});
    model.functions[0].body = {
        {"fresh", Operation{"create", {}, {}, {"fresh"}}},
        {"", Return{{"fresh"}}}};
    refuse(protocol::admitNativeLocalDefinitions(model, {realization}),
           "mathematical-formation");
  });
  cases.run("stopping finite callback retains the empty-domain result", [&] {
    auto model = fixture();
    model.functions[0].body = {{"stop", Stop{"reject"}}};
    expect(query(model, "fold", {fold()}), {{0, 1}});
  });
  cases.run("complete admission precedes a requested root query", [&] {
    auto model = fixture();
    model.functions.push_back(identityFunction("unused"));
    model.functions[1].body = {{"", Return{{"missing"}}}};
    uint64_t work = 100000;
    refuses(analyzeResourceOrigins(model, {}, "identity", work),
            "interactive-unavailable");
  });
  cases.run("finite state roots require matching callback input ports", [&] {
    auto model = fixture();
    model.functions[0].arguments[0].type = "bool";
    model.functions[0].body = {{"stop", Stop{"reject"}}};
    refuse(protocol::admitNativeLocalDefinitions(model, {fold()}),
           "mathematical-formation");
  });
  cases.run("finite state roots require matching callback output ports", [&] {
    auto model = fixture();
    model.functions[0].results.clear();
    model.functions[0].body = {{"", Return{}}};
    refuse(protocol::admitNativeLocalDefinitions(model, {fold()}),
           "mathematical-formation");
  });
  cases.run("analysis refuses absent callees and zero depth", [&] {
    auto model = fixture();
    uint64_t work = 100000;
    refuses(analyzeResourceOrigins(model, {}, "absent", work),
            "mathematical-formation");
    refuses(analyzeResourceOrigins(model, {}, "identity", work, 0),
            "mathematical-analysis-limit");
  });
  cases.run("every smaller work allowance refuses the same valid query", [&] {
    auto model = conditional();
    uint64_t work = 100000;
    take(analyzeResourceOrigins(model, {}, "identity", work));
    uint64_t cost = 100000 - work;
    require(cost < 100, "fixture accidentally exceeds small-work test");
    for (uint64_t limit = 0; limit < cost; ++limit) {
      uint64_t remaining = limit;
      refuses(analyzeResourceOrigins(model, {}, "identity", remaining),
              "mathematical-analysis-limit");
    }
    expect(take(analyzeResourceOrigins(model, {}, "identity", cost)), {{0, 0}});
    require(cost == 0, "exact allowance was not consumed");
  });
  cases.run("queries consume the caller's cumulative allowance", [&] {
    auto model = fixture();
    uint64_t work = 100000;
    take(analyzeResourceOrigins(model, {}, "identity", work));
    uint64_t allowance = 2 * (100000 - work) - 1;
    take(analyzeResourceOrigins(model, {}, "identity", allowance));
    refuses(analyzeResourceOrigins(model, {}, "identity", allowance),
            "mathematical-analysis-limit");
  });
  cases.run("cached callee height cannot hide a deeper call path", [&] {
    for (bool warmFirst : {false, true}) {
      auto model = fixture();
      for (unsigned i = 0; i < 3; ++i) {
        auto fn = identityFunction("helper" + std::to_string(i));
        fn.body = {{"call", LocalApply{i ? "helper" + std::to_string(i - 1)
                                         : "identity",
                                       {"state"},
                                       {"next"}}},
                   {"", Return{{"next"}}}};
        model.functions.push_back(fn);
      }
      auto caller = identityFunction("caller");
      caller.body = {
          {"first",
           LocalApply{warmFirst ? "identity" : "helper2", {"state"}, {"a"}}},
          {"second",
           LocalApply{warmFirst ? "helper2" : "identity", {"a"}, {"b"}}},
          {"", Return{{"b"}}}};
      model.functions.push_back(caller);
      uint64_t work = 100000;
      auto result = take(analyzeResourceOrigins(model, {}, "caller", work, 5));
      expect(result, {{0, 0}});
      require(result.depth == 5, "cached height changed");
      refuses(analyzeResourceOrigins(model, {}, "caller", work, 4),
              "mathematical-analysis-limit");
    }
  });
  cases.run("analysis owns its admitted snapshot", [&] {
    auto model = fixture();
    uint64_t work = 100000;
    auto analysis = take(ResourceOriginAnalysis::create(model, {}, work));
    model.functions[0].body = {
        {"fresh", Operation{"create", {}, {}, {"fresh"}}},
        {"", Return{{"fresh"}}}};
    expect(take(analysis->get("identity")), {{0, 0}});
    expect(query(model), {});
  });
  cases.run("cached queries consume work and retain caller depth", [&] {
    auto model = fixture();
    uint64_t work = 100000;
    auto analysis = take(ResourceOriginAnalysis::create(model, {}, work, 4));
    expect(take(analysis->get("identity")), {{0, 0}});
    uint64_t before = work;
    expect(take(analysis->get("identity", 4)), {{0, 0}});
    require(work < before, "cached query consumed no work");
    refuses(analysis->get("identity", 5), "mathematical-analysis-limit");
    refuses(analysis->get("identity"), "mathematical-analysis-limit");
  });
  cases.run("a populated cache cannot bypass exhausted work", [&] {
    uint64_t work = 100000;
    auto analysis = take(ResourceOriginAnalysis::create(fixture(), {}, work));
    take(analysis->get("identity"));
    work = 0;
    refuses(analysis->get("identity"), "mathematical-analysis-limit");
    work = 100000;
    refuses(analysis->get("identity"), "mathematical-analysis-limit");
  });
  return cases.result();
}
