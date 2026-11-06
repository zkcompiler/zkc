#include "../lib/Compiler/ConstructionBinding.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Protocol/Construction.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Language/Project.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Translation/Language.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/JSON.h"
#include <fstream>
using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace {
namespace pir = protocol_ir;

// Real formed Protocol IR, prepared by the production preparation path. The
// private summary's input facts are read from actual operations below; these
// focused controls do not bypass the public selected-proof refusal guards.
std::string message(StringRef site) {
  return (Twine("%") + site + " = protocol.exchange %value {site=\"" + site +
          "\",sender=\"P\",receiver=\"V\"} : "
          "!algebra.field<\"bls12-381.fr\">\n")
      .str();
}
std::string query(StringRef site) {
  return (Twine("%") + site + " = \"protocol.query\"(%service) {site=\"" +
          site +
          "\",owner=\"V\",method=\"draw\"} : "
          "(!protocol.service_ref<\"random.bls12-381.fr/0\">)->"
          "!algebra.field<\"bls12-381.fr\">\n" +
          "%delivery_" + site + " = protocol.exchange %" + site +
          " {site=\"delivery_" + site +
          "\",sender=\"V\",receiver=\"P\"} : "
          "!algebra.field<\"bls12-381.fr\">\n")
      .str();
}
std::string captureNames(const Twine &body, StringRef prefix) {
  auto text = body.str();
  for (StringRef name : {"value", "choice", "service"}) {
    auto from = ("%" + name).str();
    auto to = ("%" + prefix + "_" + name).str();
    size_t position = 0;
    while ((position = text.find(from, position)) != std::string::npos) {
      text.replace(position, from.size(), to);
      position += to.size();
    }
  }
  return text;
}
std::string branch(StringRef site, StringRef thenBody, StringRef elseBody) {
  auto arm = [&](StringRef label, StringRef body) {
    auto prefix = (site + "_" + label).str();
    return captureNames(
        "^arm(%value:!algebra.field<\"bls12-381.fr\">,%choice:i1,"
        "%service:!protocol.service_ref<\"random.bls12-381.fr/0\">):\n" +
            body + "\"protocol.yield\"() : ()->()\n",
        prefix);
  };
  return (Twine("\"protocol.branch\"(%choice,%value,%choice,%service) ({\n") +
          arm("then", thenBody) + "}, {\n" + arm("else", elseBody) +
          "}) {site=\"" + site +
          "\",roles=[\"P\",\"V\"],output_roles=[],alternatives=[\"then\","
          "\"else\"]} : "
          "(i1,!algebra.field<\"bls12-381.fr\">,i1,"
          "!protocol.service_ref<\"random.bls12-381.fr/0\">)->()\n")
      .str();
}
std::string repeat(StringRef body, unsigned count) {
  auto nested = captureNames(
      "^body(%i:ui64,%value:!algebra.field<\"bls12-381.fr\">,%choice:i1,"
      "%service:!protocol.service_ref<\"random.bls12-381.fr/0\">):\n" +
          body + "\"protocol.yield\"() : ()->()\n",
      "rounds");
  return (Twine("%count = \"data.index\"() {value=") + Twine(count) +
          ":ui64} : ()->ui64\n"
          "\"protocol.repeat\"(%count,%value,%choice,%service) ({\n" +
          nested +
          "}) "
          "{site=\"rounds\",carried=0:i64,maximum=3:i64,roles=[\"P\",\"V\"],"
          "carried_roles=[]} : (ui64,!algebra.field<\"bls12-381.fr\">,i1,"
          "!protocol.service_ref<\"random.bls12-381.fr/0\">)->()\n")
      .str();
}
struct TerminalFixture {
  OwningOpRef<ModuleOp> owner;
  pir::MathematicalOp source;
  SmallVector<zkc::detail::NativeTranscriptEvent> events;
  std::vector<std::pair<std::string, std::string>> draws;
};
TerminalFixture terminalFixture(MLIRContext &context, StringRef body) {
  auto text =
      (Twine("module { \"protocol.module\"() ({\n\"protocol.func\"() ({\n"
             "^entry(%value:!algebra.field<\"bls12-381.fr\">,%choice:i1,"
             "%service:!protocol.service_ref<\"random.bls12-381.fr/0\">):\n") +
       body +
       "\"protocol.return\"() : ()->()\n}) {sym_name=\"main\","
       "function_type=(!algebra.field<\"bls12-381.fr\">,i1,"
       "!protocol.service_ref<\"random.bls12-381.fr/"
       "0\">)->(),roles=[\"P\",\"V\"],"
       "input_roles=[[\"P\",\"V\"],[\"P\",\"V\"],[\"V\"]],output_roles=[]} : "
       "()->()\n"
       "}) {profile=#protocol.profile<protocol>} : ()->() }")
          .str();
  auto original = parseSourceString<ModuleOp>(text, &context);
  require(bool(original) && succeeded(admitStage(*original)),
          "terminal fixture must form");
  auto owner = mathematical::prepareProtocol(*original, false);
  require(bool(owner) && succeeded(admitStage(*owner)),
          "terminal fixture must prepare");
  auto unit = cast<pir::ProtocolModuleOp>(owner->getBody()->front());
  auto source = SymbolTable(unit).lookup<pir::MathematicalOp>("main");
  TerminalFixture result{std::move(owner), source, {}, {}};
  source.walk<WalkOrder::PreOrder>([&](Operation *op) {
    auto q = dyn_cast<pir::QueryOp>(op);
    auto m = dyn_cast<pir::ExchangeOp>(op);
    auto s = dyn_cast<pir::ConstructionStartOp>(op);
    if (!q && !m && !s)
      return;
    unsigned depth = 0;
    for (Operation *parent = op->getParentOp(); parent != source;
         parent = parent->getParentOp())
      depth += isa<pir::RepeatOp>(parent);
    std::string site = op->getAttrOfType<StringAttr>("site").str();
    zkc::detail::NativeTranscriptEvent event{site,
                                             {},
                                             q   ? q.getResult(0).getType()
                                             : m ? m.getInput().getType()
                                                 : Type(),
                                             bool(q),
                                             depth,
                                             std::nullopt};
    if (s)
      event.startInputs = SmallVector<Type>(s.getOperandTypes());
    if (q)
      result.draws.emplace_back(site, "delivery_" + site);
    result.events.push_back(std::move(event));
  });
  return result;
}
void expectTerminal(const TerminalFixture &f, ArrayRef<StringRef> expected,
                    bool selected = true) {
  auto summary = take(
      zkc::detail::summarizeConstructionTerminal(f.source, f.events, f.draws));
  SmallVector<StringRef> actual;
  for (unsigned index : summary.pending)
    actual.push_back(f.events[index].site);
  require(llvm::equal(actual, expected),
          "structured terminal frontier differs");
  require(summary.selectedControl == selected, "selected control fact differs");
}

std::string mutate(StringRef text, StringRef from, StringRef to) {
  auto result = text.str();
  auto at = result.find(from.str());
  require(at != std::string::npos, "mutation missing");
  result.replace(at, from.size(), to.str());
  return result;
}
struct Fixture {
  OwningOpRef<ModuleOp> original;
  NativeProofPolicy policy;
  NativeProofConstruction constructed;
};
Expected<Fixture> fixture(StringRef text, MLIRContext &context,
                          ArrayRef<unsigned> publicInputs = {0},
                          unsigned service = 2) {
  auto captured = language::capture({{"m", text.str(), "binding.zkc"}});
  if (!captured)
    return captured.takeError();
  auto checked = language::analyze(*captured).checkedProject();
  if (!checked)
    return checked.takeError();
  auto closed = language::closeEntry(*checked, "m::Demo");
  if (!closed)
    return closed.takeError();
  auto emitted = language::emitOriginal(*closed, context);
  if (!emitted)
    return emitted.takeError();
  auto original = parseSourceString<ModuleOp>(*emitted, &context);
  if (!original)
    return zkc::error("test-original");
  auto unit = cast<protocol_ir::ProtocolModuleOp>(original->getBody()->front());
  NativeProofPolicy policy;
  for (auto entry :
       unit.getBody().front().getOps<protocol_ir::MathematicalOp>()) {
    policy.entry = entry.getSymName().str();
    policy.producer = cast<StringAttr>(entry.getRoles()[0]).str();
    policy.validator = cast<StringAttr>(entry.getRoles()[1]).str();
  }
  policy.publicInputs.assign(publicInputs.begin(), publicInputs.end());
  policy.services = {service};
  for (auto record :
       unit.getBody().front().getOps<protocol_ir::ConstructionOp>())
    policy.construction = record.getSymName().str();
  if (policy.construction.empty())
    policy.suite = "merlin3.bls12-381.fr64be/0";
  auto selected = selectNativeProofDraws(*original, policy);
  if (!selected)
    return selected.takeError();
  auto constructed = constructNativeProof(*original, *selected);
  if (!constructed)
    return constructed.takeError();
  return Fixture{std::move(original), std::move(*selected),
                 std::move(*constructed)};
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  std::ifstream input(ZKC_FIXTURES "/language/construction-binding.zkc");
  std::string program((std::istreambuf_iterator<char>(input)), {});
  require(!program.empty(), "binding fixture missing");
  Cases cases;
  auto oneArm = message("m0") + branch("choose", query("q"), message("m1")) +
                message("m2");
  cases.run("prepared source joins incoming and other-arm messages", [&] {
    auto f = terminalFixture(context, oneArm);
    expectTerminal(f, {"m0", "m1", "m2"});
  });
  cases.run("both arms query from the same incoming frontier", [&] {
    auto f = terminalFixture(context,
                             message("m0") +
                                 branch("choose", query("q0") + message("left"),
                                        query("q1") + message("right")) +
                                 message("m2"));
    expectTerminal(f, {"left", "right", "m2"});
  });
  cases.run("nested and sequential branches use independent frontiers", [&] {
    auto f = terminalFixture(
        context,
        message("m0") +
            branch("outer", branch("inner", query("q0"), message("inner_m")),
                   message("outer_m")) +
            branch("later", query("q1"), message("later_m")) + message("last"));
    expectTerminal(f, {"m0", "inner_m", "outer_m", "later_m", "last"});
  });
  cases.run("later unconditional query clears the complete join", [&] {
    auto f =
        terminalFixture(context, oneArm + query("final_q") + message("last"));
    expectTerminal(f, {"last"});
  });
  cases.run("unselected private service queries do not clear the frontier",
            [&] {
              auto privateQuery = query("private_q");
              privateQuery.erase(privateQuery.find("%delivery_"));
              auto f = terminalFixture(
                  context, message("before") + privateQuery + message("after"));
              f.events.erase(f.events.begin() + 1);
              f.draws.clear();
              expectTerminal(f, {"before", "after"}, false);
            });
  cases.run("event-free arms deduplicate the shared incoming frontier", [&] {
    auto f =
        terminalFixture(context, message("z_first") + branch("empty", "", "") +
                                     message("a_last"));
    expectTerminal(f, {"z_first", "a_last"});
  });
  for (unsigned count : {0u, 1u, 3u})
    cases.run(
        "repeat body is one syntactic template at count " + Twine(count), [&] {
          auto f = terminalFixture(
              context,
              message("before") +
                  repeat(branch("inside", query("q"), message("body_m")),
                         count) +
                  message("after"));
          expectTerminal(f, {"before", "body_m", "after"});
          auto flat = terminalFixture(context, message("before") +
                                                   repeat(query("q"), count) +
                                                   message("after"));
          expectTerminal(flat, {"after"}, false);
        });
  cases.run("repeat inside a branch preserves the other arm", [&] {
    auto f = terminalFixture(
        context, message("before") +
                     branch("outer", repeat(query("q"), 0), message("other")));
    expectTerminal(f, {"before", "other"});
  });
  cases.run("starts are covered but are neither messages nor queries", [&] {
    auto f = terminalFixture(
        context,
        message("before") +
            "protocol.construction_start(%value) {site=\"child\","
            "roles=[\"P\",\"V\"]} : !algebra.field<\"bls12-381.fr\">\n" +
            message("after"));
    expectTerminal(f, {"before", "after"}, false);
    f.events.erase(f.events.begin() + 1);
    refuses(
        zkc::detail::summarizeConstructionTerminal(f.source, f.events, f.draws),
        "construction-binding-coverage");
  });
  for (StringRef mutation : {"absent", "absent query", "absent delivery",
                             "duplicate", "site", "kind", "payload", "depth",
                             "start", "order", "extra", "draw", "delivery"})
    cases.run("prepared coverage refuses " + mutation, [&] {
      auto f = terminalFixture(context, oneArm);
      if (mutation == "absent")
        f.events.erase(f.events.begin());
      else if (mutation == "absent query")
        f.events.erase(f.events.begin() + 1);
      else if (mutation == "absent delivery")
        f.events.erase(f.events.begin() + 2);
      else if (mutation == "duplicate") {
        auto duplicate = f.events.front();
        f.events.insert(f.events.begin(), duplicate);
      } else if (mutation == "site")
        f.events.front().site = "absent_site";
      else if (mutation == "kind")
        f.events.front().query = true;
      else if (mutation == "payload")
        f.events.front().payload = IntegerType::get(&context, 1);
      else if (mutation == "depth")
        f.events.front().depth = 1;
      else if (mutation == "start")
        f.events.front().startInputs = SmallVector<Type>{};
      else if (mutation == "order")
        std::swap(f.events.front(), f.events.back());
      else if (mutation == "extra")
        f.events.push_back(f.events.front());
      else if (mutation == "draw")
        f.draws.push_back(f.draws.front());
      else
        f.draws.front().second = "absent_delivery";
      refuses(zkc::detail::summarizeConstructionTerminal(f.source, f.events,
                                                         f.draws),
              "construction-binding-coverage");
    });
  for (bool empty : {false, true})
    cases.run(empty ? "explicit-input event-free branch stays refused"
                    : "explicit-input selected profile stays refused",
              [&] {
                auto f = terminalFixture(
                    context, empty ? branch("empty", "", "") : oneArm);
                NativeProofPolicy policy;
                policy.draws = f.draws;
                refuses(zkc::detail::analyzeConstructionBinding(
                            *f.owner, f.source,
                            f.source.getFunctionType().getInputs(), policy,
                            NativeProofBindingProfile::ExplicitInput, f.events,
                            nullptr),
                        "construction-binding-selected-control");
              });
  cases.run(
      "budget covers event input, traversal, copies and joins atomically", [&] {
        auto f = terminalFixture(context, oneArm);
        // Find the exact successful budget; every smaller allowance must
        // refuse, including the boundary after discovery and before the final
        // join.
        uint64_t sufficient = 100000;
        require(bool(take(zkc::detail::summarizeConstructionTerminal(
                              f.source, f.events, f.draws, sufficient))
                         .pending.size()),
                "fixture needs pending messages");
        uint64_t insufficient = 0;
        refuses(zkc::detail::summarizeConstructionTerminal(f.source, f.events,
                                                           f.draws, 0),
                "construction-binding-capacity");
        while (sufficient - insufficient > 1) {
          uint64_t budget = insufficient + (sufficient - insufficient) / 2;
          auto result = zkc::detail::summarizeConstructionTerminal(
              f.source, f.events, f.draws, budget);
          if (result)
            sufficient = budget;
          else {
            require(namesIdentifier(toString(result.takeError()),
                                    "construction-binding-capacity"),
                    "budget must only refuse capacity");
            insufficient = budget;
          }
        }
        for (uint64_t budget : {uint64_t(1), sufficient / 2, sufficient - 1})
          refuses(zkc::detail::summarizeConstructionTerminal(f.source, f.events,
                                                             f.draws, budget),
                  "construction-binding-capacity");
        auto exact = take(zkc::detail::summarizeConstructionTerminal(
            f.source, f.events, f.draws, sufficient));
        require(exact.pending == SmallVector<unsigned>({0, 3, 4}),
                "capacity retries must return a complete unchanged fact");
      });
  cases.run("caller cannot raise the terminal work ceiling", [&] {
    std::string body;
    for (unsigned i = 0; i < 128; ++i)
      body += message("m" + std::to_string(i));
    for (unsigned i = 0; i < 64; ++i)
      body += branch("choose_" + std::to_string(i), "", "");
    auto f = terminalFixture(context, body);
    refuses(zkc::detail::summarizeConstructionTerminal(f.source, f.events,
                                                       f.draws, 1000000),
            "construction-binding-capacity");
  });
  cases.run("native history reports the prepared structured terminal", [&] {
    auto f = terminalFixture(context, oneArm);
    NativeProofPolicy policy;
    policy.suite = "merlin3.bls12-381.fr64be/0";
    policy.draws = f.draws;
    auto report = take(zkc::detail::analyzeConstructionBinding(
        *f.owner, f.source, f.source.getFunctionType().getInputs(), policy,
        NativeProofBindingProfile::NativeHistory, f.events, nullptr));
    auto &coverage = *report.getAsObject()->getObject("coverage");
    require(printJson(*coverage.get("terminal_outside_query")) ==
                printJson(json::Array{"m0", "m1", "m2"}),
            "native history must use the structured summary");
  });
  cases.run(
      "canonical history uses real handlers and structured terminal", [&] {
        auto base = take(fixture(program, context));
        auto unit =
            cast<pir::ProtocolModuleOp>(base.original->getBody()->front());
        auto record =
            *unit.getBody().front().getOps<pir::ConstructionOp>().begin();
        SymbolTableCollection symbols;
        auto plan = take(protocol::readConstructionPlan(record, symbols));
        using Rule = protocol::ConstructionRule;
        SmallVector<Rule> starts;
        std::optional<Rule> observe, draw, delivery;
        for (const auto &rule : plan.rules) {
          if (rule.kind == Rule::Kind::Start)
            starts.push_back(rule);
          else if (rule.kind == Rule::Kind::Query)
            draw = rule;
          else if (rule.kind == Rule::Kind::Message) {
            if (is_contained(rule.sites, base.policy.draws.front().second))
              delivery = rule;
            else
              observe = rule;
          }
        }
        require(observe && draw && delivery && starts.size() == 1,
                "actual canonical handlers missing");
        auto f = terminalFixture(context, oneArm);
        plan.rules = std::move(starts);
        for (const auto &event : f.events) {
          Rule rule = event.query                            ? *draw
                      : event.site == f.draws.front().second ? *delivery
                                                             : *observe;
          rule.sites = {event.site};
          plan.rules.push_back(std::move(rule));
        }
        auto policy = base.policy;
        policy.draws = f.draws;
        auto report = take(zkc::detail::analyzeConstructionBinding(
            *base.constructed.module, f.source,
            f.source.getFunctionType().getInputs(), policy,
            NativeProofBindingProfile::CanonicalHashHistory, f.events, &plan));
        auto &coverage = *report.getAsObject()->getObject("coverage");
        require(printJson(*coverage.get("terminal_outside_query")) ==
                    printJson(json::Array{"m0", "m1", "m2"}),
                "canonical history must use the structured summary");
        require(coverage.getArray("transitions")->size() == 6,
                "all actual canonical transitions must still be checked");
      });
  auto analyze = [&](StringRef text, NativeProofBindingProfile profile) {
    auto f = fixture(text, context);
    if (!f)
      return Expected<json::Value>(f.takeError());
    return analyzeNativeProofBinding(*f->original, *f->constructed.module,
                                     f->policy, profile);
  };
  for (auto profile : {NativeProofBindingProfile::NativeHistory,
                       NativeProofBindingProfile::CanonicalHashHistory,
                       NativeProofBindingProfile::ExplicitInput})
    cases.run("branch-free terminal summary retains the flat suffix " +
                  Twine(static_cast<unsigned>(profile)),
              [&] {
                auto text =
                    profile == NativeProofBindingProfile::NativeHistory
                        ? mutate(program, "construction Derived<History>;",
                                 "construction "
                                 "fiat_shamir(\"merlin3.bls12-381.fr64be/"
                                 "0\",challenges);")
                    : profile == NativeProofBindingProfile::ExplicitInput
                        ? mutate(program, "construction Derived<History>;",
                                 "construction Derived<Explicit>;")
                        : program;
                auto f = take(fixture(text, context));
                auto report = take(analyzeNativeProofBinding(
                    *f.original, *f.constructed.module, f.policy, profile));
                std::string bytes = printJson(report);
                json::Array flat;
                for (const auto &item :
                     *report.getAsObject()->getArray("occurrences")) {
                  const auto &event = *item.getAsObject();
                  if (*event.getBoolean("query"))
                    flat.clear();
                  else if (!llvm::any_of(f.policy.draws, [&](const auto &draw) {
                             return draw.second == *event.getString("site");
                           }))
                    flat.push_back(event.getString("site")->str());
                }
                (*report.getAsObject()->getObject(
                    "coverage"))["terminal_outside_query"] = std::move(flat);
                require(printJson(report) == bytes,
                        "structured summary differs from the legacy flat "
                        "terminal suffix");
              });
  cases.run("actual canonical hash history", [&] {
    auto report =
        take(analyze(program, NativeProofBindingProfile::CanonicalHashHistory));
    auto &coverage = *report.getAsObject()->getObject("coverage");
    require(coverage.getString("hash") == "hash.sha256",
            "hash primitive missing");
    require(coverage.getArray("transitions")->size() == 5,
            "root/start/commit/query/terminal coverage");
    require(coverage.getArray("terminal_outside_query")->size() == 1,
            "terminal absorption is not a subsequent query");
  });
  auto explicitSource = mutate(program, "construction Derived<History>;",
                               "construction Derived<Explicit>;");
  cases.run("actual stateless explicit-input request", [&] {
    auto report =
        take(analyze(explicitSource, NativeProofBindingProfile::ExplicitInput));
    auto &coverage = *report.getAsObject()->getObject("coverage");
    require(coverage.getArray("transitions")->size() == 1,
            "explicit request count");
    require(coverage.getArray("terminal_outside_query")->size() == 1,
            "terminal distinction missing");
  });
  cases.run("explicit input is not a history claim", [&] {
    refuses(analyze(explicitSource,
                    NativeProofBindingProfile::CanonicalHashHistory),
            "construction-binding-coverage");
  });
  for (auto replacement :
       {std::pair<StringRef, StringRef>{"tag(2),concat(unpack(t),encode(v))",
                                        "tag(2),unpack(t)"},
        {"tag(3),concat(unpack(t),encode(v))", "tag(3),unpack(t)"},
        {"tag(3),concat(unpack(t),encode(v))",
         "tag(3),concat(encode(v),unpack(t))"},
        {"return (State(next),sample(next));", "return (t,sample(next));"},
        {"tag(4),unpack(t)", "tag(3),unpack(t)"}})
    cases.run(
        "history refuses omitted/reset/reordered data: " + replacement.first,
        [&] {
          refuses(
              analyze(mutate(program, replacement.first, replacement.second),
                      NativeProofBindingProfile::CanonicalHashHistory),
              "construction-binding-coverage");
        });
  cases.run("arithmetic dependence is not canonical coverage", [&] {
    refuses(analyze(mutate(program, "tag(2),concat(unpack(t),encode(v))",
                           "tag(2),concat(unpack(t),encode(v-v))"),
                    NativeProofBindingProfile::CanonicalHashHistory),
            "construction-binding-encoding");
  });
  cases.run("stateless query cannot omit its public input", [&] {
    refuses(analyze(mutate(explicitSource, "return State(encode(v));",
                           "return State(empty());"),
                    NativeProofBindingProfile::ExplicitInput),
            "construction-binding-coverage");
  });
  cases.run("native installed history", [&] {
    auto native = mutate(
        program, "construction Derived<History>;",
        "construction fiat_shamir(\"merlin3.bls12-381.fr64be/0\",challenges);");
    auto report =
        take(analyze(native, NativeProofBindingProfile::NativeHistory));
    require(report.getAsObject()->getString("profile") == "native-history",
            "native profile");
    auto &coverage = *report.getAsObject()->getObject("coverage");
    require(coverage.getArray("terminal_outside_query")->size() == 1,
            "native terminal absorption is not a subsequent query");
  });
  cases.run("local handlers do not inherit installed history", [&] {
    refuses(analyze(program, NativeProofBindingProfile::NativeHistory),
            "construction-binding-profile");
  });
  cases.run("complete report recomputation refuses changed evidence", [&] {
    auto f = take(fixture(program, context));
    auto report = take(analyzeNativeProofBinding(
        *f.original, *f.constructed.module, f.policy,
        NativeProofBindingProfile::CanonicalHashHistory));
    auto parsed = take(parseNaturalJson(printJson(report), 8 * 1024 * 1024, 64,
                                        "test-json", "test-capacity"));
    require(equalNaturalJson(report, parsed),
            "report JSON round trip changes meaning");
    auto repeated = take(analyzeNativeProofBinding(
        *f.original, *f.constructed.module, f.policy,
        NativeProofBindingProfile::CanonicalHashHistory));
    require(equalNaturalJson(report, repeated),
            "binding recomputation is nondeterministic");
    auto checked = checkNativeProofBinding(
        *f.original, *f.constructed.module, f.policy,
        NativeProofBindingProfile::CanonicalHashHistory, printJson(report));
    if (checked)
      throw std::runtime_error(toString(std::move(checked)));
    (*report.getAsObject())["candidate_sha256"] = "changed";
    auto error = checkNativeProofBinding(
        *f.original, *f.constructed.module, f.policy,
        NativeProofBindingProfile::CanonicalHashHistory, printJson(report));
    require(bool(error) && namesIdentifier(toString(std::move(error)),
                                           "construction-binding-report"),
            "changed report identity accepted");
  });
  auto byteProgram = mutate(program, "public:F@(P,V)", "public:Bytes@(P,V)");
  for (unsigned i = 0; i < 3; ++i)
    byteProgram = mutate(byteProgram, "fn start(t:State,v:F)",
                         "fn start(t:State,v:Bytes)");
  byteProgram = mutate(byteProgram, "tag(2),concat(unpack(t),encode(v))",
                       "tag(2),concat(unpack(t),frame(v))");
  byteProgram = mutate(byteProgram, "return State(encode(v));",
                       "return State(frame(v));");
  byteProgram = mutate(byteProgram, "interface Chain", R"(
fn length(x:Bytes)->index=primitive("bytes.length");
fn length_code(x:index)->Bytes=primitive("encoding.index_uleb128");
fn frame(x:Bytes)->Bytes{return concat(length_code(length(x)),x);}
interface Chain)");
  cases.run("canonical actual-length framing", [&] {
    take(analyze(byteProgram, NativeProofBindingProfile::CanonicalHashHistory));
  });
  cases.run("unframed variable bytes refuse", [&] {
    refuses(
        analyze(mutate(byteProgram, "return concat(length_code(length(x)),x);",
                       "return x;"),
                NativeProofBindingProfile::CanonicalHashHistory),
        "construction-binding-encoding");
  });
  cases.run("constant length does not frame a variable input", [&] {
    refuses(analyze(mutate(byteProgram, "length_code(length(x))",
                           "length_code(32)"),
                    NativeProofBindingProfile::CanonicalHashHistory),
            "construction-binding-encoding");
  });
  std::ifstream schnorrInput(ZKC_FIXTURES
                             "/language/construction-binding-schnorr.zkc");
  std::string schnorr((std::istreambuf_iterator<char>(schnorrInput)), {});
  require(!schnorr.empty(), "Schnorr binding fixture missing");
  for (bool history : {true, false})
    cases.run(
        history ? "Schnorr canonical history" : "Schnorr explicit inputs", [&] {
          auto text = history ? schnorr
                              : mutate(schnorr, "Derived<History>",
                                       "Derived<Explicit>");
          auto f = take(fixture(text, context, {0, 1}, 4));
          auto profile = history
                             ? NativeProofBindingProfile::CanonicalHashHistory
                             : NativeProofBindingProfile::ExplicitInput;
          auto report = take(analyzeNativeProofBinding(
              *f.original, *f.constructed.module, f.policy, profile));
          if (auto error =
                  checkNativeProofBinding(*f.original, *f.constructed.module,
                                          f.policy, profile, printJson(report)))
            throw std::runtime_error(toString(std::move(error)));
        });
  cases.run("changed actual terminal acceptance is not binding evidence", [&] {
    auto f = take(fixture(program, context));
    bool changed = false;
    f.constructed.module->walk([&](algebra::FieldEqualOp op) {
      op->setOperand(1, op->getOperand(0));
      changed = true;
    });
    require(changed, "actual acceptance predicate missing");
    refuses(analyzeNativeProofBinding(
                *f.original, *f.constructed.module, f.policy,
                NativeProofBindingProfile::CanonicalHashHistory),
            "native-proof-correspondence");
  });
  cases.run("history cannot drop terminal observation", [&] {
    auto text =
        mutate(program,
               "on message {commitment,response}(t,value){return "
               "H::observe(t,value);}",
               "on message commitment(t,value){return H::observe(t,value);}"
               "on message response(t,value){return t;}");
    refuses(analyze(text, NativeProofBindingProfile::CanonicalHashHistory),
            "construction-binding-coverage");
  });
  cases.run("mixed-direction message grouping refuses before binding", [&] {
    auto f = take(fixture(program, context));
    auto unit =
        cast<protocol_ir::ProtocolModuleOp>(f.original->getBody()->front());
    auto record =
        *unit.getBody().front().getOps<protocol_ir::ConstructionOp>().begin();
    Builder builder(&context);
    StringRef delivery = f.policy.draws.front().second;
    std::string response = "label_" + llvm::toHex("response", true) + "_0";
    unsigned changed = 0;
    SmallVector<Attribute> rules;
    for (auto attr : record.getRules()) {
      auto rule = cast<DictionaryAttr>(attr);
      auto sites = rule.getAs<ArrayAttr>("sites");
      if (sites.size() == 1 &&
          cast<StringAttr>(sites[0]).getValue() == response) {
        ++changed;
        continue;
      }
      if (sites.size() == 1 &&
          cast<StringAttr>(sites[0]).getValue() == delivery) {
        ++changed;
        auto handler = SymbolTable(unit).lookup<func::FuncOp>(
            rule.getAs<FlatSymbolRefAttr>("handler").getValue());
        auto type = handler.getFunctionType();
        SmallVector<Type> inputs(type.getInputs());
        inputs.push_back(inputs.back());
        handler.setType(builder.getFunctionType(inputs, type.getResults()));
        handler.getBody().front().addArgument(inputs.back(), handler.getLoc());
        NamedAttrList grouped(rule);
        grouped.set("sites", builder.getStrArrayAttr({delivery, response}));
        auto payload = rule.getAs<ArrayAttr>("payload");
        grouped.set("payload", builder.getArrayAttr({payload[0], payload[0]}));
        rule = grouped.getDictionary(&context);
      }
      rules.push_back(rule);
    }
    require(changed == 2,
            "grouping must replace both actual message selectors");
    record.setRulesAttr(builder.getArrayAttr(rules));
    refuses(constructNativeProof(*f.original, f.policy),
            "native-proof-construction-message-group");
  });
  auto tupleSource =
      mutate(program, "send P->V(secret);", "send P->V((secret,secret));");
  tupleSource = mutate(tupleSource, "return last==first+c;",
                       "let (left,right)=first; return last==left+c;");
  tupleSource = mutate(
      tupleSource,
      "on message {commitment,response}(t,value){return H::observe(t,value);}",
      "on message commitment(t,value){let (a,b)=value; return "
      "H::observe(H::observe(t,a),b);}"
      "on message response(t,value){return H::observe(t,value);}");
  cases.run("whole grouped payload is covered by actual nested hashes", [&] {
    take(analyze(tupleSource, NativeProofBindingProfile::CanonicalHashHistory));
  });
  cases.run("a grouped handler cannot omit its second payload", [&] {
    refuses(analyze(mutate(tupleSource, "H::observe(H::observe(t,a),b)",
                           "H::observe(t,a)"),
                    NativeProofBindingProfile::CanonicalHashHistory),
            "construction-binding-coverage");
  });
  return cases.result();
}
