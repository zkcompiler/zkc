#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Implementations.h"
#include "zkc/Target/Catalog.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace zkc::protocol;
namespace {
unsigned checks = 0;
void require(bool condition, StringRef message) {
  ++checks;
  if (!condition) {
    errs() << message << '\n';
    std::exit(1);
  }
}
template <typename T> T accept(Expected<T> result) {
  if (!result) {
    errs() << toString(result.takeError()) << '\n';
    std::exit(1);
  }
  ++checks;
  return std::move(*result);
}
void refuse(Error result, StringRef code) {
  require(bool(result), "expected refusal");
  auto actual = toString(std::move(result));
  if (actual != code) {
    errs() << "expected " << code << ", got " << actual << '\n';
    std::exit(1);
  }
}
template <typename T> void refuse(Expected<T> result, StringRef code) {
  require(!result, "expected refusal");
  refuse(result.takeError(), code);
}
void succeeds(Error result) {
  if (result) {
    errs() << toString(std::move(result)) << '\n';
    std::exit(1);
  }
  ++checks;
}
BoundOperation physical(StringRef contract, std::vector<std::string> arguments,
                        StringRef implementation) {
  return accept(resolveBinding(
      {contract.str(), std::move(arguments), implementation.str()}, true));
}
void defaultIs(StringRef contract, std::vector<std::string> arguments,
               StringRef expected) {
  BindingApplication binding{contract.str(), std::move(arguments), ""};
  require(accept(defaultImplementation(binding)) == expected,
          "selected default changed");
  auto candidates =
      accept(zkc::target::installedCandidates().implementations(binding));
  require(candidates == std::vector<std::string>{expected.str()},
          "candidate policy changed the default");
}

const zkc::generic::Scope &scopeFor(StringRef contract) {
  for (const auto &operation : boundOperationContracts())
    if (operation.name == contract)
      return operation.signature.scope;
  errs() << "missing logical contract " << contract << '\n';
  std::exit(1);
}

void selectorPolicies(const ImplementationCatalog &installed) {
  using Compatibility = ImplementationDescriptor::Compatibility;
  // The Scalar projection is scope term 1 but the call supplies only its Group
  // root. Both preference and exact-domain restriction must use the projection.
  auto projected = *installed.find("curve.msm", "dalek/curve.msm");
  projected.identity = "custom/projected-msm";
  projected.providerTerm = 1;
  projected.domain = "ristretto255.scalar";
  auto catalog = accept(ImplementationCatalog::create(
      {projected},
      {{projected.contract, projected.provider, projected.identity}}));
  BindingApplication msm{"curve.msm", {"ristretto255.group"}, ""};
  require(accept(catalog.defaultFor(msm))->identity == projected.identity,
          "provider selection used a raw argument offset");
  const auto &msmScope = scopeFor(msm.contract);
  auto identities = accept(resolveStaticArguments(msmScope, msm.arguments));
  succeeds(checkImplementationArguments(projected, msmScope, identities));
  auto withoutPreference =
      accept(ImplementationCatalog::create({projected}, {}));
  refuse(withoutPreference.defaultFor(msm), "binding-implementation");
  require(withoutPreference.find(msm.contract, projected.identity),
          "missing preference removed descriptor applicability");
  refuse(catalog.defaultFor({"curve.msm", {}, ""}), "binding-static-arity");
  refuse(catalog.defaultFor({"curve.msm", {"bls12-381.g1"}, ""}),
         "binding-implementation");

  auto bad = projected;
  bad.providerTerm = 2;
  refuse(ImplementationCatalog::create({bad}, {}),
         "implementation-catalog-policy");
  refuse(checkImplementationArguments(bad, msmScope, identities),
         "binding-implementation");
  bad = projected;
  bad.providerTerm = 0; // The restriction is a Field, not this Group root.
  refuse(ImplementationCatalog::create({bad}, {}),
         "implementation-catalog-policy");
  bad = projected;
  bad.compatibility = Compatibility::Transcript;
  refuse(ImplementationCatalog::create({bad}, {}),
         "implementation-catalog-policy");
  for (unsigned index : {1u, 2u}) {
    bad = *installed.find("fixed_vector.dot", "plonky3/fixed_vector.dot");
    bad.providerTerm = index; // Nat root and applied Type term respectively.
    refuse(ImplementationCatalog::create({bad}, {}),
           "implementation-catalog-policy");
  }
  bad = *installed.find("transcript.observe.field",
                        "arkworks/transcript.observe.field");
  bad.providerTerm = 1; // A Field cannot select a Transcript policy.
  refuse(ImplementationCatalog::create({bad}, {}),
         "implementation-catalog-policy");
  bad.compatibility = Compatibility::Nominal;
  bad.providerTerm =
      2; // Codec is a Domain kind, but never a provider selector.
  refuse(ImplementationCatalog::create({bad}, {}),
         "implementation-catalog-policy");
  bad.providerTerm =
      0; // Transcript requires its distinct compatibility policy.
  refuse(ImplementationCatalog::create({bad}, {}),
         "implementation-catalog-policy");

  // A later formal Domain root also selects a preference. The different suite
  // provider still fails nominal applicability: preference grants no support.
  auto payloadSelected = bad;
  payloadSelected.providerTerm = 1;
  payloadSelected.identity = "custom/payload-selected";
  auto payloadCatalog = accept(ImplementationCatalog::create(
      {payloadSelected},
      {{payloadSelected.contract, "arkworks", payloadSelected.identity}}));
  BindingApplication observe{"transcript.observe.field",
                             {"spongefish0.7.4.keccak.bls12-381.fr64be/1",
                              "bls12-381.fr", "zkcv.field.bls12-381.fr/1"},
                             ""};
  require(accept(payloadCatalog.defaultFor(observe))->identity ==
              payloadSelected.identity,
          "later Domain root did not select the provider preference");
  auto payloads = accept(
      resolveStaticArguments(scopeFor(observe.contract), observe.arguments));
  refuse(checkImplementationArguments(payloadSelected,
                                      scopeFor(observe.contract), payloads),
         "binding-implementation");

  // Exercise the same scope validator used by catalog creation on a reordered
  // structural scope; this does not install a new operation or realization.
  zkc::generic::Scope leading{{{"T"}, {"N"}, {"F"}}, {"Type", "Nat", "Field"}};
  auto selected = *installed.find("field.add", "plonky3/field.add");
  selected.providerTerm = 2;
  selected.domain = "koala-bear";
  succeeds(checkImplementationScope(selected, leading));
  auto leadingIdentities =
      accept(resolveStaticArguments(leading, {"bool", "7", "koala-bear"}));
  succeeds(checkImplementationArguments(selected, leading, leadingIdentities));
  leadingIdentities[2] = "koala-bear.ext8-binomial3";
  refuse(checkImplementationArguments(selected, leading, leadingIdentities),
         "binding-implementation");
  selected.providerTerm = 0;
  refuse(checkImplementationScope(selected, leading),
         "implementation-catalog-policy");

  auto malformed = msmScope;
  malformed.terms[1].parent = 1;
  refuse(checkImplementationScope(projected, malformed),
         "implementation-catalog-policy");
  malformed = msmScope;
  malformed.terms[1].name = "MissingMember";
  refuse(checkImplementationScope(projected, malformed),
         "implementation-catalog-policy");
  malformed = msmScope;
  malformed.terms[1].arguments = std::vector<unsigned>{0};
  refuse(checkImplementationScope(projected, malformed),
         "implementation-catalog-policy");
  // Constant roots participate in resolution but consume no call argument.
  auto constant = msmScope;
  constant.constants[0] = "ristretto255.group";
  succeeds(checkImplementationScope(projected, constant));
  auto constantIdentities = accept(resolveStaticArguments(constant, {}));
  succeeds(
      checkImplementationArguments(projected, constant, constantIdentities));
  constant.constants[0] = "ristretto255.scalar";
  refuse(checkImplementationScope(projected, constant),
         "implementation-catalog-policy");

  auto independent = *installed.find("indices.length", "native/indices.length");
  zkc::generic::Scope structural{
      {{"T"}, {"N"}, {"fixed_vector", {}, std::vector<unsigned>{0, 1}}},
      {"Type", "Nat", "Type"}};
  succeeds(checkImplementationScope(independent, structural));
  auto statics =
      accept(resolveStaticArguments(structural, {"field:bls12-381.fr", "4"}));
  succeeds(checkImplementationArguments(independent, structural, statics));
  require(statics[2] == "fixed_vector<field:bls12-381.fr,4>",
          "Independent policy erased structural statics");
  statics.pop_back();
  refuse(checkImplementationArguments(independent, structural, statics),
         "binding-implementation");
  refuse(checkImplementationScope(independent, leading),
         "implementation-catalog-policy");
  independent.providerTerm = 1;
  refuse(checkImplementationScope(independent, structural),
         "implementation-catalog-policy");
  independent.providerTerm = 0;
  independent.domain = "bls12-381.fr";
  refuse(checkImplementationScope(independent, structural),
         "implementation-catalog-policy");

  // Transcript selection can follow leading Type/Nat terms. Their identities
  // do not act as fields, but the actual payload Field must still be
  // compatible.
  zkc::generic::Scope transcript{
      {{"Payload"}, {"N"}, {"Suite"}, {"Field"}, {"Codec"}},
      {"Type", "Nat", "Transcript", "Field", "Codec"}};
  auto transcriptSelected = *installed.find(
      "transcript.observe.field", "spongefish/transcript.observe.field");
  transcriptSelected.providerTerm = 2;
  succeeds(checkImplementationScope(transcriptSelected, transcript));
  auto transcriptIdentities = accept(resolveStaticArguments(
      transcript, {"field:ristretto255.scalar", "4", observe.arguments[0],
                   "bls12-381.fr", "zkcv.field.bls12-381.fr/1"}));
  succeeds(checkImplementationArguments(transcriptSelected, transcript,
                                        transcriptIdentities));
  transcriptIdentities[3] = "ristretto255.scalar";
  transcriptIdentities[4] = "zkcv.field.ristretto255.scalar/1";
  refuse(checkImplementationArguments(transcriptSelected, transcript,
                                      transcriptIdentities),
         "binding-implementation");
}

} // namespace

int main() {
  const auto &catalog = installedImplementations();
  selectorPolicies(catalog);
  require(&catalog == &installedImplementations(), "installation not retained");
  for (StringRef name : {"field.future", "index.future", "indices.future",
                         "transcript.future", "external.future"}) {
    refuse(checkImplementation(name, ("arkworks/" + name).str()),
           "binding-contract");
    refuse(checkImplementation(name, ("native/" + name).str()),
           "binding-contract");
    refuse(defaultImplementation({name.str(), {}, ""}), "binding-contract");
  }
  // A declared contract omitted from this installation acquires no support.
  auto empty = accept(ImplementationCatalog::create({}, {}));
  accept(resolveBinding({"field.add", {"bls12-381.fr"}, ""}, false));
  require(!empty.find("field.add", "arkworks/field.add"),
          "declaration implicitly registered an implementation");
  refuse(empty.defaultFor({"field.add", {"bls12-381.fr"}, ""}),
         "binding-implementation");
  refuse(checkImplementation("field.add", "spongefish/field.add"),
         "binding-implementation");
  refuse(checkImplementation("bool.and", "dalek/bool.and"),
         "binding-implementation");
  refuse(checkImplementation("curve.add", "plonky3/curve.add"),
         "binding-implementation");
  refuse(checkImplementation("field.add", "arkworks/field.mul"),
         "binding-implementation");
  refuse(
      resolveBinding({"field.add", {"bls12-381.fr"}, "dalek/field.add"}, true),
      "binding-implementation");
  require(
      !implementationProviderSupports("arkworks", "bls12-381.future") &&
          !implementationProviderSupports("arkworks-future", "bls12-381.fr"),
      "nominal provider membership fell through by prefix");

  defaultIs("bool.and", {}, "arkworks/bool.and");
  defaultIs("index.constant", {}, "native/index.constant");
  defaultIs("indices.append", {}, "native/indices.append");
  defaultIs("external.openvm.sample", {}, "native/external.openvm.sample");
  defaultIs("field.add", {"bls12-381.fr"}, "arkworks/field.add");
  defaultIs("vector.dot", {"bls12-381.fr"}, "arkworks/vector.dot");
  const StringRef pairwise = "arkworks-pairwise/vector.dot";
  auto ordinaryDot =
      physical("vector.dot", {"bls12-381.fr"}, "arkworks/vector.dot");
  auto pairwiseDot = physical("vector.dot", {"bls12-381.fr"}, pairwise);
  require(ordinaryDot.inputs == pairwiseDot.inputs &&
              ordinaryDot.outputs == pairwiseDot.outputs,
          "algorithm choice changed physical ports");
  require(catalog.find("vector.dot", pairwise) &&
              catalog.find("vector.dot", pairwise)->identity == pairwise &&
              catalog.find("vector.dot", pairwise)->representations.empty(),
          "exact algorithm identity or unchanged representations lost");
  for (bool physical : {false, true}) {
    accept(resolveBinding({"vector.dot", {"bls12-381.fr"}, pairwise.str()},
                          physical));
    for (StringRef domain : {"bn254.fr", "ristretto255.scalar", "koala-bear",
                             "koala-bear.ext8-binomial3"})
      refuse(resolveBinding({"vector.dot", {domain.str()}, pairwise.str()},
                            physical),
             "binding-implementation");
    for (StringRef contract : {"vector.mul", "vector.sum", "field.add"})
      refuse(resolveBinding({contract.str(), {"bls12-381.fr"}, pairwise.str()},
                            physical),
             "binding-implementation");
    refuse(resolveBinding({"vector.dot", {}, pairwise.str()}, physical),
           "binding-static-arity");
  }
  refuse(checkImplementation("vector.dot", "arkworks-pairwise/vector.dot/1"),
         "binding-implementation");
  refuse(checkImplementation("vector.mul", "arkworks-pairwise/vector.mul"),
         "binding-implementation");
  defaultIs("field.add", {"bn254.fr"}, "arkworks/field.add");
  defaultIs("random.draw", {"koala-bear.ext8-binomial3"},
            "plonky3/random.draw");
  defaultIs("field.add", {"ristretto255.scalar"}, "dalek/field.add");
  defaultIs("field.add", {"koala-bear"}, "plonky3/field.add");
  defaultIs("field.add", {"koala-bear.ext8-binomial3"}, "plonky3/field.add");
  defaultIs("curve.msm", {"ristretto255.group"}, "dalek/curve.msm");
  defaultIs("pcs.open", {"multilinear.kzg.bls12-381/1"}, "arkworks/pcs.open");
  defaultIs("oracle.open", {"rows.merkle-keccak256.koala-bear/1"},
            "plonky3/oracle.open");
  defaultIs("resource_unit.pass", {"session.slot"},
            "logical/resource_unit.pass");

  require(
      physical("bool.and", {}, "arkworks/bool.and").outputs[0].representation ==
          "native.bool/1",
      "representation spelling selected the provider");
  const std::pair<StringRef, StringRef> suites[] = {
      {"merlin3.bls12-381.fr64be/1", "arkworks"},
      {"merlin3.ristretto255.scalar64le/1", "dalek"},
      {"merlin3.koala-bear.ext8-binomial3.rejection31le/1", "plonky3"},
      {"spongefish0.7.4.keccak.bls12-381.fr64be/1", "spongefish"}};
  for (const auto &[suite, provider] : suites) {
    std::string impl = (provider + "/transcript.challenge").str();
    defaultIs("transcript.challenge", {suite.str()}, impl);
    auto ports = physical("transcript.challenge", {suite.str()}, impl);
    require(ports.inputs[0].representation == "host.resource/1",
            "shared host representation changed nominal provider selection");
  }
  const std::string spongefish = "spongefish0.7.4.keccak.bls12-381.fr64be/1";
  const std::string extension =
      "merlin3.koala-bear.ext8-binomial3.rejection31le/1";
  physical("transcript.observe.field",
           {spongefish, "bls12-381.fr", "zkcv.field.bls12-381.fr/1"},
           "spongefish/transcript.observe.field");
  physical("transcript.observe.field",
           {extension, "koala-bear", "zkcv.field.koala-bear/1"},
           "plonky3/transcript.observe.field");
  physical("transcript.observe.group",
           {spongefish, "bls12-381.g1", "zkcv.group.bls12-381.g1/1"},
           "spongefish/transcript.observe.group");
  refuse(resolveBinding({"transcript.observe.field",
                         {spongefish, "ristretto255.scalar",
                          "zkcv.field.ristretto255.scalar/1"},
                         "spongefish/transcript.observe.field"},
                        true),
         "binding-implementation");
  refuse(resolveBinding({"transcript.challenge",
                         {spongefish},
                         "arkworks/transcript.challenge"},
                        true),
         "binding-implementation");

  for (StringRef operation : {"fixed_vector.from_vector",
                              "fixed_vector.to_vector", "fixed_vector.dot"}) {
    const std::string implementation = ("plonky3/" + operation).str();
    for (StringRef size : {"0", "4", "17", "1048576"}) {
      defaultIs(operation, {"koala-bear", size.str()}, implementation);
      auto ports =
          physical(operation, {"koala-bear", size.str()}, implementation);
      unsigned fixedPorts = 0;
      for (const auto *side : {&ports.inputs, &ports.outputs})
        for (const auto &port : *side)
          if (port.kind == "fixed_vector") {
            ++fixedPorts;
            require(port.spelling() == ("fixed_vector<field:koala-bear," +
                                        size + ">@plonky3.fixed-vector/1")
                                           .str(),
                    "natural index was not retained in the physical port");
          }
      require(fixedPorts == (operation == "fixed_vector.dot" ? 2u : 1u),
              "fixed vector port count changed");
    }
    BindingApplication unsupported{operation.str(), {"bls12-381.fr", "4"}, ""};
    accept(resolveBinding(unsupported, false));
    refuse(defaultImplementation(unsupported), "binding-implementation");
    unsupported.implementation = ("arkworks/" + operation).str();
    refuse(resolveBinding(unsupported, true), "binding-implementation");
    unsupported.arguments[0] = "koala-bear.ext8-binomial3";
    unsupported.implementation = implementation;
    accept(resolveBinding({operation.str(), unsupported.arguments, ""}, false));
    refuse(resolveBinding(unsupported, true), "binding-implementation");
  }

  const StringRef msbContracts[] = {"poly.product_sum",  "poly.product_round",
                                    "poly.boundary",     "poly.round_evaluate",
                                    "poly.fold",         "poly.evaluate",
                                    "poly.empty_point",  "poly.append_point",
                                    "vector.from_table", "vector.to_table"};
  for (StringRef operation : msbContracts) {
    defaultIs(operation, {"bls12-381.fr"}, ("arkworks/" + operation).str());
    auto ports = physical(operation, {"bls12-381.fr"},
                          ("arkworks-msb/" + operation).str());
    for (const auto *side : {&ports.inputs, &ports.outputs})
      for (const auto &port : *side)
        if (port.kind == "table")
          require(port.representation == "arkworks.mle-msb/1",
                  "MSB layout lost");
  }
  refuse(resolveBinding({"poly.round_evaluate",
                         {"bn254.fr"},
                         "arkworks-msb/poly.round_evaluate"},
                        true),
         "binding-implementation");
  refuse(checkImplementation("field.add", "arkworks-msb/field.add"),
         "binding-implementation");

  struct DiagonalCase {
    StringRef contract, domain, implementation, representation;
    bool output;
    unsigned port;
  };
  const DiagonalCase diagonals[] = {
      {"vector.mul", "bls12-381.fr", "arkworks-diagonal/vector.mul",
       "arkworks.fr-diagonal/1", true, 0},
      {"vector.dot", "bls12-381.fr", "arkworks-diagonal/vector.dot",
       "arkworks.fr-diagonal/1", false, 1},
      {"curve.scale_each", "ristretto255.group",
       "dalek-diagonal/curve.scale_each", "dalek.ristretto-diagonal/1", true,
       0},
      {"curve.msm", "ristretto255.group", "dalek-diagonal/curve.msm",
       "dalek.ristretto-diagonal/1", false, 1}};
  for (const auto &row : diagonals) {
    BindingApplication binding{row.contract.str(), {row.domain.str()}, ""};
    auto alternatives =
        zkc::target::installedCandidates().diagonalImplementations(binding);
    require(alternatives == std::vector<std::string>{row.implementation.str()},
            "diagonal candidate not selected by exact metadata");
    binding.implementation = row.implementation.str();
    auto ports = accept(zkc::target::resolveDiagonalImplementation(binding));
    require(
        (row.output ? ports.outputs : ports.inputs)[row.port].representation ==
            row.representation,
        "diagonal layout on wrong port");
    unsigned count = 0;
    for (const auto *side : {&ports.inputs, &ports.outputs})
      for (const auto &port : *side)
        count += isDiagonalRepresentation(port.representation);
    require(count == 1, "diagonal representation escaped its declared port");
  }
  require(!isDiagonalRepresentation("arkworks.fr-diagonal/2") &&
              !isDiagonalRepresentation("future.diagonal/1"),
          "diagonal representation recognized by spelling");
  require(zkc::target::installedCandidates()
              .diagonalImplementations({"vector.mul", {"bn254.fr"}, ""})
              .empty(),
          "diagonal provider inherited BN254 support");
  refuse(
      resolveBinding(
          {"vector.mul", {"bn254.fr"}, "arkworks-diagonal/vector.mul"}, true),
      "binding-implementation");
  auto vartime =
      physical("curve.msm", {"ristretto255.group"}, "dalek-vartime/curve.msm");
  require(!isDiagonalRepresentation(vartime.inputs[1].representation),
          "vartime choice implies a diagonal layout");
  refuse(resolveBinding(
             {"curve.msm", {"bls12-381.g1"}, "dalek-vartime/curve.msm"}, true),
         "binding-implementation");
  refuse(
      checkImplementation("curve.scale_each", "dalek-vartime/curve.scale_each"),
      "binding-implementation");

  // Descriptor identity is opaque. Naming an implementation after another
  // provider neither changes its applicability nor implies a layout policy.
  auto renamed = *catalog.find("vector.mul", "arkworks-diagonal/vector.mul");
  renamed.identity = "native.unrelated-choice/7";
  auto custom = accept(ImplementationCatalog::create({renamed}, {}));
  require(custom.find("vector.mul", renamed.identity),
          "opaque identity refused");
  require(!custom.preferred("vector.mul", "arkworks"),
          "applicability manufactured a default");
  auto dense = physical("vector.mul", {"bls12-381.fr"}, "arkworks/vector.mul");
  succeeds(applyImplementationRepresentations(renamed, dense));
  require(dense.outputs[0].representation == "arkworks.fr-diagonal/1",
          "layout inferred from implementation spelling");
  auto bad = renamed;
  bad.contract = "field.future";
  refuse(ImplementationCatalog::create({bad}, {}),
         "implementation-catalog-contract");
  bad = renamed;
  bad.compatibility = ImplementationDescriptor::Compatibility::Independent;
  refuse(ImplementationCatalog::create({bad}, {}),
         "implementation-catalog-policy");
  bad = renamed;
  bad.domain = "ristretto255.scalar";
  refuse(ImplementationCatalog::create({bad}, {}),
         "implementation-catalog-policy");
  bad = renamed;
  bad.provider = "future";
  refuse(ImplementationCatalog::create({bad}, {}),
         "implementation-catalog-entry");
  bad = renamed;
  bad.representations[0].identity = "arkworks.fr-diagonal/future";
  refuse(ImplementationCatalog::create({bad}, {}),
         "implementation-catalog-representation");
  refuse(applyImplementationRepresentations(bad, dense),
         "binding-representation");
  bad = renamed;
  bad.representations[0].port = 4;
  refuse(ImplementationCatalog::create({bad}, {}),
         "implementation-catalog-representation");
  refuse(ImplementationCatalog::create({renamed, renamed}, {}),
         "implementation-catalog-entry");
  refuse(ImplementationCatalog::create({renamed},
                                       {{"vector.mul", "arkworks", "missing"}}),
         "implementation-catalog-default");
  refuse(ImplementationCatalog::create(
             {renamed}, {{"vector.mul", "dalek", renamed.identity}}),
         "implementation-catalog-default");

  for (StringRef operation : {"resource_unit.create", "resource_unit.pass",
                              "resource_unit.consume"}) {
    physical(operation, {"session.slot"}, ("logical/" + operation).str());
    refuse(checkImplementation(operation, ("arkworks/" + operation).str()),
           "binding-implementation");
  }
  BindingApplication relayout{
      "table.relayout",
      {"bls12-381.fr", "arkworks.mle-lsb/1", "arkworks.mle-msb/1"},
      "arkworks/table.relayout"};
  auto conversion = accept(resolveBinding(relayout, true));
  succeeds(zkc::target::checkDirectConversion(relayout, conversion.inputs[0],
                                              conversion.outputs[0]));
  relayout.arguments[2] = relayout.arguments[1];
  refuse(resolveBinding(relayout, true), "binding-conversion");
  outs() << checks << " implementation policy checks passed\n";
}
