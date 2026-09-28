#include "zkc/Contracts/Domains.h"
#include "zkc/Mathematical/Installation.h"
#include "zkc/Mathematical/Subject.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace zkc::mathematical;
namespace r = zkc::mathematical::raw;
namespace p = zkc::protocol;

namespace {
void check(bool condition, StringRef message) {
  if (!condition) {
    errs() << message << '\n';
    std::exit(1);
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
  check(!value, "unexpected admission");
  auto message = toString(value.takeError());
  check(message == code, message);
}
void refuses(Error failure, StringRef code) {
  check(bool(failure), "unexpected admission");
  auto message = toString(std::move(failure));
  check(message == code, message);
}
void success(Error failure) {
  if (failure) {
    errs() << toString(std::move(failure)) << '\n';
    std::exit(1);
  }
}
uint64_t domain(const Installation &installation, StringRef name) {
  const auto &domains = installation.manifest().domains;
  for (size_t i = 0; i < domains.size(); ++i)
    if (domains[i].name == name)
      return i;
  check(false, "missing installed domain");
  return 0;
}

r::Subject groupCalculation(const Installation &installation) {
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
  module.wires = {{{0}, 0, group}};
  // Shared algebra does not grant the verifier access to the private scalar.
  // In a region, new results prepend the local reference context.
  r::Region region{{{0}},
                   {r::PureOperation{{1}, {}, json::Object{}, {}},
                    r::PureOperation{{2}, {}, json::Object{}, {{0}, {1}}}},
                   {{0}}};
  module.definitions = {
      {0,
       2,
       {},
       {{{{0}}, scalar}},
       {{{{1}}, group}},
       {},
       {{r::Pure{region}, r::Message{0, {0}, {}, {0}, {1}, {0}}},
        r::Return{{{0}}}}}};
  module.entry = {{0}, {}, {{0}, {1}}, {}};
  return source;
}

r::Subject entropyQueries(const Installation &installation) {
  r::Subject source;
  source.manifest = installation.manifest();
  auto &module = source.module;
  module.roles = {"prover", "verifier"};
  module.types = {
      {0, r::NominalType{{domain(installation, "bls12-381.fr")}, "field", {}}},
      {0, r::NominalType{
              {domain(installation, "bls12-381.fr")}, "nonzero_field", {}}}};
  const r::TypeUse scalar{{0}, {}}, nonzero{{1}, {}};
  module.capabilityTypes = {{{0}, 0, {}, scalar}, {{1}, 0, {}, nonzero}};
  module.roots = {{{{0}, {}}, {{0}}}, {{{1}, {}}, {{1}}}};
  module.definitions = {{0,
                         2,
                         {{{{0}, {}}, {{0}}}, {{{1}, {}}, {{1}}}},
                         {},
                         {{{{1}}, nonzero}},
                         {},
                         {{r::Query{0, {0}, {0}, {}}, r::Query{1, {0}, {0}, {}},
                           r::Query{2, {1}, {1}, {}}},
                          r::Return{{{0}}}}}};
  module.entry = {{0}, {}, {{0}, {1}}, {{0}, {1}}};
  return source;
}
} // namespace

int main() {
  const std::vector<p::BindingApplication> samplers{
      {"random.draw", {"bls12-381.fr"}, ""},
      {"random.draw_nonzero", {"bls12-381.fr"}, ""}};
  auto services = take(Installation::create({}, {}, samplers));
  auto queries = entropyQueries(services);
  auto admittedQueries = take(admit(queries, services));
  const auto &querySteps = admittedQueries.instances()[0].typed.body.steps;
  check(querySteps[0].outputBindings[0] != querySteps[1].outputBindings[0],
        "repeated queries merged their binding occurrences");
  check(querySteps[0].capabilities == querySteps[1].capabilities,
        "repeated queries changed capability root");
  auto aliases = queries;
  aliases.module.definitions[0].capabilities.push_back(
      aliases.module.definitions[0].capabilities[0]);
  aliases.module.entry.capabilities.push_back({0});
  std::get<r::Query>(aliases.module.definitions[0].body.steps[1]).capability = {
      2};
  auto admittedAliases = take(admit(aliases, services));
  check(admittedAliases.instances()[0].roots ==
            std::vector<uint32_t>({0, 1, 0}),
        "capability aliases created independent roots");
  const auto *draw = services.serviceBinding(services.manifest().services[0]);
  check(draw && draw->transition.contract == "random.draw" &&
            draw->state.spelling() == "rng:bls12-381.fr",
        "service lost its installed state transition");
  auto invalidQuery = queries;
  invalidQuery.module.capabilityTypes[1].result = {{0}, {}};
  refuses(admit(invalidQuery, services), "math-installed-service-signature");
  invalidQuery = queries;
  std::get<r::Query>(invalidQuery.module.definitions[0].body.steps[0]).owner = {
      1};
  refuses(admit(invalidQuery, services), "math-capability-permission");
  invalidQuery = queries;
  invalidQuery.manifest.services[0].digest.assign(64, '0');
  refuses(admit(invalidQuery, services), "math-installed-package");
  check(!services.serviceBinding(invalidQuery.manifest.services[0]),
        "forged service selected a state transition");
  for (auto name : {"random.vector", "transcript.challenge", "field.add"})
    refuses(Installation::create({}, {}, {{name, {"bls12-381.fr"}, ""}}),
            "entropy-service-contract");
  refuses(Installation::create({}, {}, {samplers[0], samplers[0]}),
          "math-installed-service-duplicate");
  const std::vector<p::BindingApplication> bindings = {
      {"field.add", {"bls12-381.fr"}, ""},
      {"curve.generator", {"bls12-381.g1"}, ""},
      {"curve.scale", {"bls12-381.g1"}, ""},
      {"curve.equal", {"bls12-381.g1"}, ""}};
  const auto *codec =
      p::installedDomains().defaultCodec("group", "bls12-381.g1");
  check(codec, "missing canonical group codec");
  auto installation = take(Installation::create(bindings, {codec->identity}));
  auto independent = take(Installation::create(bindings, {codec->identity}));
  check(installation.manifest().operations[0].digest ==
            independent.manifest().operations[0].digest,
        "installation descriptor is not reproducible");
  for (size_t i = 0; i < bindings.size(); ++i) {
    const auto &identity = installation.manifest().operations[i];
    check(installation.binding(identity) &&
              installation.binding(identity)->contract == bindings[i].contract,
          "operation realization mapping changed");
    success(installation.identity(Registry::Category::Operation, identity,
                                  installation.manifest()));
    refuses(installation.identity(Registry::Category::Operation, identity, {}),
            "math-installed-prerequisite");
  }
  auto source = groupCalculation(installation);
  auto missingScalar = source.manifest;
  missingScalar.domains.erase(missingScalar.domains.begin() +
                              domain(installation, "bls12-381.fr"));
  refuses(installation.identity(
              Registry::Category::Domain,
              source.manifest.domains[domain(installation, "bls12-381.g1")],
              missingScalar),
          "math-installed-prerequisite");
  refuses(installation.identity(Registry::Category::Wire,
                                source.manifest.wires[0], missingScalar),
          "math-installed-prerequisite");
  auto generatorOnly = take(Installation::create({bindings[1]}, {}));
  check(domain(generatorOnly, "bls12-381.fr") <
            generatorOnly.manifest().domains.size(),
        "associated scalar package was not installed");
  auto subject = take(admit(source, installation));
  const auto &nodes = subject.instances()[0].typed.body.steps[0].region->nodes;
  check(nodes[0].outputs[0].roles == std::vector<uint32_t>({0, 1}) &&
            nodes[1].outputs[0].roles == std::vector<uint32_t>({0}),
        "unused private capture tainted generator or exposed private scaling");
  auto altered = source;
  altered.manifest.operations[0].digest.assign(64, '0');
  refuses(admit(altered, installation), "math-installed-package");
  check(!installation.binding(altered.manifest.operations[0]),
        "forged identity selected a realization");
  altered = source;
  altered.module.operations[2].arguments[1] = {{1}, {}};
  refuses(admit(altered, installation), "math-installed-operation-signature");
  altered = source;
  std::swap(altered.manifest.operations[0], altered.manifest.operations[2]);
  refuses(admit(altered, installation), "math-installed-operation-signature");
  altered = source;
  altered.manifest.domains.push_back(altered.manifest.domains.front());
  refuses(admit(altered, installation), "math-duplicate-package");
  for (auto resource : {"rng", "nonce"}) {
    altered = source;
    std::get<r::NominalType>(altered.module.types[0].body).name = resource;
    refuses(admit(altered, installation), "math-installed-nominal-resource");
  }
  altered = source;
  altered.module.operations[0].purity = p::OperationPurity::Ordered;
  refuses(admit(altered, installation), "math-operation-contract");
  altered = source;
  altered.module.wires[0].type = {{0}, {}};
  refuses(admit(altered, installation), "math-installed-wire-signature");
  altered = source;
  std::get<r::Return>(altered.module.definitions[0].body.terminal).values = {
      {2}};
  refuses(admit(altered, installation), "math-operand-type");
  altered = source;
  std::get<r::Return>(altered.module.definitions[0].body.terminal).values = {
      {1}};
  refuses(admit(altered, installation), "math-availability");
  altered = source;
  auto &region =
      std::get<r::Pure>(altered.module.definitions[0].body.steps[0]).region;
  std::get<r::PureOperation>(region.nodes[0]).attributes =
      json::Object{{"value", 1}};
  refuses(admit(altered, installation), "math-installed-attributes");
  for (const auto *operation : {"field.inverse", "unknown.call"})
    refuses(Installation::create({{operation, {"bls12-381.fr"}, ""}}, {}),
            "math-installed-operation-subset");
  refuses(Installation::create({{"curve.commit", {"bls12-381.g1"}, ""}}, {}),
          "math-installed-operation-subset");
  refuses(Installation::create(
              {{"field.add", {"bls12-381.fr"}, "arkworks/field.add"}}, {}),
          "math-installed-operation-subset");
  refuses(Installation::create({bindings[0], bindings[0]}, {}),
          "math-installed-duplicate-operation");
  refuses(Installation::create({}, {"not.installed"}), "math-installed-codec");
  auto otherField =
      take(Installation::create({{"field.add", {"bn254.fr"}, ""}}, {}));
  altered = source;
  altered.manifest.domains[domain(installation, "bls12-381.fr")] =
      otherField.manifest().domains[0];
  refuses(admit(altered, installation), "math-installed-package");
  auto withBothFields = bindings;
  withBothFields.push_back({"field.add", {"bn254.fr"}, ""});
  auto both = take(Installation::create(withBothFields, {codec->identity}));
  altered = groupCalculation(both);
  std::get<r::NominalType>(altered.module.types[0].body).domain = {
      domain(both, "bn254.fr")};
  refuses(admit(altered, both), "math-installed-operation-signature");
  outs() << "installed mathematical contracts: passed\n";
}
