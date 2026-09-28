#include "zkc/Contracts/Domains.h"
#include "zkc/Mathematical/Placement.h"
#include "zkc/Source/Codec.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace zkc::mathematical;
namespace r = zkc::mathematical::raw;
namespace p = zkc::protocol;
namespace s = zkc::source;
namespace {
unsigned failures = 0, checks = 0;
void check(bool condition, StringRef message) {
  ++checks;
  if (!condition) {
    ++failures;
    errs() << message << '\n';
  }
}
template <class T> T take(Expected<T> value) {
  if (!value) {
    errs() << toString(value.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*value);
}
template <class T> void refuses(Expected<T> value, StringRef code) {
  if (value) {
    check(false, "unexpected placement admission");
    return;
  }
  auto message = toString(value.takeError());
  check(message == code, message);
}
uint64_t domain(const Installation &installation, StringRef name) {
  const auto &domains = installation.manifest().domains;
  for (size_t i = 0; i < domains.size(); ++i)
    if (domains[i].name == name)
      return i;
  std::abort();
}
Installation install() {
  const auto &domains = p::installedDomains();
  return take(Installation::create(
      {{"field.add", {"bls12-381.fr"}, ""},
       {"curve.generator", {"bls12-381.g1"}, ""},
       {"curve.scale", {"bls12-381.g1"}, ""},
       {"curve.equal", {"bls12-381.g1"}, ""},
       {"field.mul", {"bls12-381.fr"}, ""},
       {"field.from_nonzero", {"bls12-381.fr"}, ""},
       {"curve.add", {"bls12-381.g1"}, ""}},
      {domains.defaultCodec("field", "bls12-381.fr")->identity,
       domains.defaultCodec("group", "bls12-381.g1")->identity,
       domains.defaultCodec("nonzero_field", "bls12-381.fr")->identity},
      {{"random.draw", {"bls12-381.fr"}, ""},
       {"random.draw_nonzero", {"bls12-381.fr"}, ""}}));
}
r::Subject comparison(const Installation &installation) {
  r::Subject source;
  source.manifest = installation.manifest();
  auto &module = source.module;
  module.roles = {"prover", "verifier"};
  module.types = {
      {0, r::NominalType{{domain(installation, "bls12-381.fr")}, "field", {}}},
      {0, r::NominalType{{domain(installation, "bls12-381.g1")}, "group", {}}},
      {0, r::FinType{Static::literal(2)}}};
  const r::TypeUse scalar{{0}, {}}, group{{1}, {}}, boolean{{2}, {}};
  const auto pure = p::OperationPurity::Total;
  module.operations = {{{0}, 0, {}, {scalar, scalar}, scalar, pure, {}},
                       {{1}, 0, {}, {}, group, pure, {}},
                       {{2}, 0, {}, {group, scalar}, group, pure, {}},
                       {{3}, 0, {}, {group, group}, boolean, pure, {}}};
  module.wires = {{{0}, 0, scalar}, {{1}, 0, group}};
  // The private capture is unused. The generator remains available at the
  // verifier, while the initial public argument has independent role values.
  r::Region generator{
      {{1}}, {r::PureOperation{{1}, {}, json::Object{}, {}}}, {{0}}};
  r::Region compare{{{0}, {1}, {2}},
                    {r::PureOperation{{2}, {}, json::Object{}, {{1}, {0}}},
                     r::PureOperation{{2}, {}, json::Object{}, {{2}, {3}}},
                     r::PureOperation{{3}, {}, json::Object{}, {{1}, {0}}}},
                    {{0}}};
  module.definitions = {
      {0,
       2,
       {},
       {{{{0}, {1}}, scalar}, {{{0}}, scalar}},
       {{{{1}}, boolean}, {{{0}, {1}}, scalar}},
       {},
       {{r::Pure{generator}, r::Message{0, {0}, {}, {0}, {1}, {1}},
         r::Pure{compare}},
        r::Return{{{0}, {1}}}}}};
  module.entry = {{0}, {}, {{0}, {1}}, {}};
  return source;
}
Placement placed(const r::Subject &raw, const Installation &installation) {
  return take(place(raw, installation));
}
r::Subject sigma(const Installation &installation) {
  auto source = comparison(installation);
  auto &module = source.module;
  const r::TypeUse scalar{{0}, {}}, group{{1}, {}}, nonzero{{3}, {}};
  const auto pure = p::OperationPurity::Total;
  module.types.push_back(
      {0, r::NominalType{
              {domain(installation, "bls12-381.fr")}, "nonzero_field", {}}});
  module.operations.push_back({{4}, 0, {}, {scalar, scalar}, scalar, pure, {}});
  module.operations.push_back({{5}, 0, {}, {nonzero}, scalar, pure, {}});
  module.operations.push_back({{6}, 0, {}, {group, group}, group, pure, {}});
  module.wires.push_back({{2}, 0, nonzero});
  module.capabilityTypes = {{{0}, 0, {}, scalar}, {{1}, 0, {}, nonzero}};
  module.roots = {{{{0}, {}}, {{0}}}, {{{1}, {}}, {{1}}}};
  auto &definition = module.definitions[0];
  definition.arguments = {
      {{{0}}, scalar}, {{{0}, {1}}, group}, {{{0}, {1}}, group}};
  definition.results = {};
  definition.capabilities = {{{{0}, {}}, {{0}}}, {{{1}, {}}, {{1}}}};
  module.entry.capabilities = {{0}, {1}};
  r::Region commitment{{{0}, {2}},
                       {r::PureOperation{{2}, {}, json::Object{}, {{1}, {0}}}},
                       {{0}}};
  r::Region response{{{0}, {4}, {5}},
                     {r::PureOperation{{5}, {}, json::Object{}, {{0}}},
                      r::PureOperation{{4}, {}, json::Object{}, {{0}, {3}}},
                      r::PureOperation{{0}, {}, json::Object{}, {{3}, {0}}}},
                     {{0}}};
  r::Region verifier{{{0}, {8}, {4}, {2}, {9}},
                     {r::PureOperation{{5}, {}, json::Object{}, {{3}}},
                      r::PureOperation{{2}, {}, json::Object{}, {{2}, {1}}},
                      r::PureOperation{{2}, {}, json::Object{}, {{6}, {1}}},
                      r::PureOperation{{6}, {}, json::Object{}, {{5}, {0}}},
                      r::PureOperation{{3}, {}, json::Object{}, {{2}, {0}}}},
                     {{0}}};
  definition.body = {{r::Query{0, {0}, {0}, {}}, r::Pure{commitment},
                      r::Message{1, {1}, {}, {0}, {1}, {0}},
                      r::Query{2, {1}, {1}, {}},
                      r::Message{3, {2}, {}, {1}, {0}, {0}}, r::Pure{response},
                      r::Message{4, {0}, {}, {0}, {1}, {0}}, r::Pure{verifier},
                      r::Guard{5, {1}, {0}}},
                     r::Return{}};
  return source;
}
const s::Body &body(const Placement &placed) {
  return *placed.target.module()->protocols.at(0).body;
}
// Deliberately permissive admission fixture: its Subject must not smuggle a
// package identity into a concrete native executable installation.
class UntrustedRegistry final : public Registry {
public:
  Error identity(Category, const r::Identity &,
                 const r::Manifest &) const override {
    return Error::success();
  }
  Error domainType(const r::Identity &, const TypeShape &) const override {
    return Error::success();
  }
  Expected<OperationFacts> operation(const r::Identity &,
                                     const OperationSignature &,
                                     const TypeTable &,
                                     const r::Manifest &) const override {
    return OperationFacts{p::OperationPurity::Total, {}};
  }
  Error wire(const r::Identity &, ArrayRef<NormalStatic>, TypeId,
             const TypeTable &, const r::Manifest &) const override {
    return Error::success();
  }
  Error service(const r::Identity &, const CapabilitySignature &,
                const TypeTable &, const r::Manifest &) const override {
    return Error::success();
  }
  Error attributes(const r::Identity &, ArrayRef<NormalStatic>,
                   const json::Value &) const override {
    return Error::success();
  }
};
} // namespace

int main(int argc, char **argv) {
  auto installation = install();
  const bool emitSigma = argc == 2 && StringRef(argv[1]) == "--sigma";
  auto raw = emitSigma ? sigma(installation) : comparison(installation);
  auto result = placed(raw, installation);
  if (argc == 2 && (StringRef(argv[1]) == "--emit" || emitSigma)) {
    outs() << json::Value(take(encode(result))) << '\n';
    return 0;
  }
  const auto &instructions = body(result);
  check(instructions.size() == 4, "placement changed ordered layout");
  const auto *generator = instructions.at(0).get<s::Pure>();
  check(generator && generator->role == "verifier" &&
            generator->captures.empty(),
        "unused private capture tainted public generator placement");
  const auto *message = instructions.at(1).get<s::Message>();
  check(message && message->input == "value_0_role_0" &&
            message->output == "value_3_role_1",
        "message did not create fresh receiver");
  const auto *compare = instructions.at(2).get<s::Pure>();
  check(compare && compare->role == "verifier" &&
            compare->captures.size() == 3 &&
            compare->captures[0].name == "value_3_role_1" &&
            compare->captures[2].name == "value_0_role_1",
        "received value collapsed to verifier public input");
  const auto *returned = instructions.at(3).get<s::Return>();
  check(returned &&
            returned->values == s::Names({"value_0_role_0", "value_4_role_1",
                                          "value_3_role_1"}),
        "sender alias or role-major result order changed");
  check(result.witness.operations.size() == 3 &&
            result.witness.operations[0].first == 1,
        "unused total operation was materialized");
  check(result.witness.sites.size() == 1 &&
            result.witness.sites[0].kind == "message",
        "pure wrapper became an effect");
  check(result.witness.results.size() == 3 &&
            result.witness.results[0].role == 0 &&
            result.witness.results[0].sourcePort == 1 &&
            result.witness.results[1].role == 1 &&
            result.witness.results[1].targetPort == 0 &&
            result.witness.results[2].targetPort == 1,
        "result map lost role-local port indices");
  check(result.witness.target ==
            take(placementTargetDigest(*result.target.module())),
        "target custody digest changed");
  auto encoded = take(encode(result.witness));
  check(encoded.getAsObject()->getArray("components")->size() ==
            result.witness.components.size(),
        "component witness encoding omitted scoped values");
  bool innerOutput = false, outerOutput = false;
  for (const auto &component : result.witness.components) {
    const auto &key = component.component;
    innerOutput |= key.source.regions == std::vector<uint32_t>({0, 0}) &&
                   key.source.binding == 1;
    outerOutput |= key.source.regions.empty() && key.source.binding == 2;
    check(!(key.source.regions == std::vector<uint32_t>({0, 0}) &&
            key.source.binding == 0),
          "unused capture entered required component domain");
  }
  check(innerOutput && outerOutput,
        "pure yield alias lost one defining binding");

  auto permuted = raw;
  permuted.module.entry.roles = {{1}, {0}};
  auto reordered = placed(permuted, installation);
  check(body(reordered)[0].get<s::Pure>()->role == "prover" &&
            body(reordered)[1].get<s::Message>()->sender == "verifier",
        "closed role substitution was ignored");

  auto passthrough = raw;
  auto &definition = passthrough.module.definitions[0];
  definition.results = {{{{0}, {1}}, {{0}, {}}}, {{{0}, {1}}, {{0}, {}}}};
  definition.body = {{r::Pure{r::Region{{{0}}, {}, {{0}, {0}}}}},
                     r::Return{{{0}, {1}}}};
  auto aliases = placed(passthrough, installation);
  check(body(aliases).size() == 3, "pass-through pure regions were erased");
  for (size_t i = 0; i < 2; ++i) {
    const auto *pure = body(aliases)[i].get<s::Pure>();
    check(pure && pure->body.size() == 1 && pure->outputs.size() == 2 &&
              pure->body[0].get<s::Yield>()->values ==
                  s::Names(2, "value_0_role_" + std::to_string(i)),
          "duplicate pass-through yields introduced fake computation");
  }

  auto query = raw;
  query.module.capabilityTypes = {{{0}, 0, {}, {{0}, {}}}};
  query.module.roots = {{{{0}, {}}, {{0}}}, {{{0}, {}}, {{1}}}};
  auto &queries = query.module.definitions[0];
  queries.capabilities = {{{{0}, {}}, {{0}}}, {{{0}, {}}, {{0}}}};
  query.module.entry.capabilities = {{0}, {0}};
  queries.results = {};
  queries.body = {{r::Query{0, {0}, {0}, {}}, r::Query{1, {0}, {1}, {}}},
                  r::Return{}};
  auto roots = placed(query, installation);
  const auto *first = body(roots)[0].get<s::Query>();
  const auto *second = body(roots)[1].get<s::Query>();
  check(first && second && first->root == second->root &&
            first->outputs != second->outputs,
        "capability aliases changed root identity or merged occurrences");
  check(roots.target.module()->roots.size() == 2 &&
            roots.witness.roots.size() == 2 &&
            roots.target.module()->bindings.size() == 1,
        "unused roots or service binding coverage changed");
  check(roots.witness.sites.size() == 2, "unused query results erased effects");

  auto stopped = raw;
  stopped.module.definitions[0].body.terminal =
      r::Stop{1, {1}, r::StopReason::Incomplete};
  auto terminal = placed(stopped, installation);
  const auto *stop = body(terminal).back().get<s::Stop>();
  check(stop && stop->reason == "incomplete" &&
            terminal.witness.results.size() == 3,
        "stop changed reason or erased declared result interface");

  auto tuple = passthrough;
  std::get<r::Pure>(tuple.module.definitions[0].body.steps[0])
      .region.nodes.push_back(r::Tuple{{{0}}});
  // Keep the tuple discarded; unsupported constructors cannot disappear under
  // DCE.
  std::get<r::Pure>(tuple.module.definitions[0].body.steps[0])
      .region.outputs = {{1}, {1}};
  refuses(place(take(admit(tuple, installation)), installation),
          "math-placement-node-subset");
  auto repeat = query;
  repeat.module.definitions[0].body = {
      {r::Repeat{0,
                 Static::literal(0),
                 {},
                 {},
                 {},
                 std::make_shared<const r::Body>(r::Body{{}, r::Return{}})}},
      r::Return{}};
  refuses(place(take(admit(repeat, installation)), installation),
          "math-placement-step-subset");
  auto unusedDefinition = query;
  unusedDefinition.module.definitions.push_back(repeat.module.definitions[0]);
  refuses(place(unusedDefinition, installation),
          "math-placement-definition-subset");
  auto selfMessage = raw;
  auto &selfSend =
      std::get<r::Message>(selfMessage.module.definitions[0].body.steps[1]);
  selfSend.receiver = selfSend.sender;
  refuses(place(selfMessage, installation), "math-message-roles");
  auto extraRole = raw;
  extraRole.module.roles.push_back("unused");
  refuses(place(take(admit(extraRole, installation)), installation),
          "math-placement-role-subset");
  refuses(
      place(take(admit(raw, installation)), installation, AdmissionBudget{0}),
      "math-admission-limit");
  auto spoofed = raw;
  spoofed.manifest.operations[1].digest.assign(64, '0');
  refuses(place(take(admit(spoofed, UntrustedRegistry{})), installation),
          "math-installed-package");
  auto sigmaResult = placed(sigma(installation), installation);
  check(body(sigmaResult).size() == 10 &&
            body(sigmaResult)[8].get<s::Guard>() &&
            body(sigmaResult)[8].get<s::Guard>()->role == "verifier",
        "Sigma failed to retain verifier guard");
  check(sigmaResult.witness.sites.size() == 6 &&
            sigmaResult.witness.roots.size() == 2,
        "Sigma lost query, message or guard occurrences");
  outs() << checks << " mathematical placement checks; " << failures
         << " failures\n";
  return failures ? 1 : 0;
}
