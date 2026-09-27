#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <map>
#include <set>

using namespace llvm;
using namespace zkc;
using namespace zkc::protocol;
namespace {
unsigned checks = 0;
void require(bool condition, StringRef detail) {
  ++checks;
  if (!condition) {
    errs() << detail << '\n';
    std::exit(1);
  }
}
template <typename T> T accept(Expected<T> result) {
  if (!result) {
    errs() << toString(result.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*result);
}
template <typename T> void refuse(Expected<T> result, StringRef reason) {
  require(!result, "expected refusal");
  require(toString(result.takeError()) == reason, reason);
}

struct Records {
  std::vector<NominalDomain> domains{
      {"test.f1", "Field", {}, {"Field", "CommRing"}},
      {"test.f2", "Field", {}, {"PrimeField"}},
      {"test.g", "Group", {{"Scalar", "test.f1"}}, {"ScalarAction"}}};
  std::vector<LogicalTypeInstance> logicalTypes{
      {"table", "test.f1"}, {"table", "test.f2"}, {"bool", ""}};
  std::vector<CodecIdentity> codecs{{"test.codec1", "table", "test.f1"},
                                    {"test.codec2", "table", "test.f2"},
                                    {"test.bool", "bool", ""}};
  std::vector<DomainRepresentation> reps{
      {"test.lsb/1", "table", "test.f1", true, "lsb"},
      {"test.msb/1", "table", "test.f1", false, "msb"},
      {"test.other/1", "table", "test.f2", false, "lsb"},
      {"test.bool/1", "bool", "", true, ""}};
  std::vector<DefaultProvider> providers{{"test.f1", "custom"}};
  Expected<DomainCatalog> build() const {
    return DomainCatalog::create(domains, logicalTypes, codecs, reps,
                                 providers);
  }
};

void malformedCatalogs() {
  auto reject = [](auto mutate, StringRef reason) {
    Records records;
    mutate(records);
    refuse(records.build(), reason);
    // Validation is deterministic and cannot leave a partially installed
    // catalog.
    refuse(records.build(), reason);
  };
  reject([](auto &r) { r.domains.push_back(r.domains[0]); },
         "duplicate catalog identity");
  reject([](auto &r) { r.codecs.push_back(r.codecs[0]); },
         "duplicate catalog identity");
  reject([](auto &r) { r.codecs[0].identity = r.domains[0].identity; },
         "duplicate catalog identity");
  reject([](auto &r) { r.domains[0].identity.clear(); },
         "invalid catalog identity");
  reject([](auto &r) { r.codecs[0].identity = "bad@identity"; },
         "invalid catalog identity");
  reject([](auto &r) { r.domains[0].identity = std::string(257, 'a'); },
         "invalid catalog identity");
  reject([](auto &r) { r.domains[0].sort = "Unknown"; }, "invalid domain sort");
  reject([](auto &r) { r.domains[0].sort = "Codec"; }, "invalid domain sort");
  reject([](auto &r) { r.domains[2].associated[0].identity = "missing"; },
         "invalid associated identity");
  reject([](auto &r) { r.domains[2].associated[0].identity = "test.g"; },
         "invalid associated identity");
  reject([](auto &r) { r.domains[2].associated[0].identity = "test.codec1"; },
         "invalid associated identity");
  reject([](auto &r) { r.domains[2].associated[0].member = "ChallengeField"; },
         "invalid associated identity");
  reject([](auto &r) { r.domains[0].associated = {{"Scalar", "test.f1"}}; },
         "invalid associated identity");
  reject(
      [](auto &r) { r.domains[2].associated.push_back({"Scalar", "test.f2"}); },
      "duplicate associated member");
  reject([](auto &r) { r.domains[0].capabilities.push_back("Field"); },
         "duplicate capability fact");
  reject([](auto &r) { r.domains[0].capabilities.push_back("ScalarAction"); },
         "invalid capability fact");
  reject([](auto &r) { r.domains[0].capabilities.push_back("UnknownFact"); },
         "invalid capability fact");
  reject([](auto &r) { r.domains[0].capabilities.push_back("Encodes.bool"); },
         "invalid capability fact");
  reject([](auto &r) { r.logicalTypes.push_back(r.logicalTypes[0]); },
         "duplicate logical type instance");
  for (const auto &type :
       std::vector<LogicalTypeInstance>{{"unknown", "test.f1"},
                                        {"table", ""},
                                        {"table", "test.g"},
                                        {"table", "missing"},
                                        {"table", "test.codec1"},
                                        {"bool", "test.f1"},
                                        {"variant", ""},
                                        {"resource_unit", ""}})
    reject([&](auto &r) { r.logicalTypes.push_back(type); },
           "invalid logical type instance");
  reject([](auto &r) { r.logicalTypes.clear(); },
         "unadmitted codec payload type");
  reject(
      [](auto &r) {
        r.logicalTypes.clear();
        r.codecs.clear();
      },
      "unadmitted representation type");
  reject([](auto &r) { r.codecs[0].kind = "field"; },
         "unadmitted codec payload type");
  reject([](auto &r) { r.reps[0].kind = "field"; },
         "unadmitted representation type");
  reject([](auto &r) { r.codecs[0].domain = "test.g"; },
         "invalid codec payload domain");
  reject([](auto &r) { r.codecs[0].domain = "missing"; },
         "invalid codec payload domain");
  reject([](auto &r) { r.codecs[0].domain.clear(); },
         "invalid codec payload domain");
  reject([](auto &r) { r.codecs[2].domain = "test.f1"; },
         "invalid codec payload domain");
  reject([](auto &r) { r.codecs[0].kind = "unknown"; },
         "invalid codec payload domain");
  reject([](auto &r) { r.codecs[0].kind = "rng"; },
         "invalid codec payload kind");
  reject([](auto &r) { r.reps[0].identity.clear(); },
         "invalid representation identity");
  reject([](auto &r) { r.reps[0].identity = "bad@representation"; },
         "invalid representation identity");
  reject([](auto &r) { r.reps[0].domain = "test.g"; },
         "invalid representation domain");
  reject([](auto &r) { r.reps[0].domain = "missing"; },
         "invalid representation domain");
  reject([](auto &r) { r.reps[0].domain.clear(); },
         "invalid representation domain");
  reject([](auto &r) { r.reps[0].kind = "unknown"; },
         "invalid representation domain");
  reject([](auto &r) { r.reps[3].domain = "test.f1"; },
         "invalid representation domain");
  reject([](auto &r) { r.reps.push_back(r.reps[0]); },
         "duplicate representation");
  reject([](auto &r) { r.reps[1].isDefault = true; },
         "ambiguous representation default");
  reject([](auto &r) { r.reps[1].layout = "lsb"; },
         "ambiguous representation layout");
  reject([](auto &r) { r.reps[0].layout = "bad@layout"; },
         "invalid representation layout");
  for (StringRef identity : {"missing", "test.codec1", ""})
    reject([&](auto &r) { r.providers[0].domain = identity.str(); },
           "invalid provider domain");
  for (StringRef provider : {"", "bad@provider", "custom/field.add"})
    reject([&](auto &r) { r.providers[0].provider = provider.str(); },
           "invalid default provider");
  reject([](auto &r) { r.providers.push_back(r.providers[0]); },
         "duplicate default provider");
  reject([](auto &r) { r.providers.push_back({"test.f1", "other"}); },
         "duplicate default provider");
}

void closedCatalogs() {
  Records records;
  const auto catalog = accept(records.build());
  require(catalog.domain("test.g")->sort == "Group", "custom domain record");
  require(catalog.associatedIdentity("test.g", "Scalar") == "test.f1",
          "custom association");
  require(catalog.associatedIdentity("test.g", "Unknown").empty() &&
              catalog.associatedIdentity("missing", "Scalar").empty(),
          "unsupported association stays unknown");
  require(catalog.identitySort("missing").empty() &&
              !catalog.domain("missing") && !catalog.codec("missing"),
          "uninstalled identities stay unknown");
  require(catalog.hasFact("ScalarAction", {"test.g"}) &&
              !catalog.hasFact("ScalarAction", {"test.f1"}) &&
              !catalog.hasFact("Field", {}) &&
              !catalog.hasFact("Field", {"test.f1", "test.f2"}) &&
              !catalog.hasFact("Unknown", {"test.f1"}),
          "capabilities use exact installed facts and arity");
  require(catalog.hasFact("PrimeField", {"test.f2"}) &&
              !catalog.hasFact("Field", {"test.f2"}),
          "catalog facts do not invent implications");
  require(catalog.hasFact("Encodes.table", {"test.codec1", "test.f1"}) &&
              !catalog.hasFact("Encodes.table", {"test.codec1", "test.f2"}) &&
              !catalog.hasFact("Encodes.field", {"test.codec1", "test.f1"}) &&
              !catalog.hasFact("Encodes.table", {"test.codec1"}) &&
              !catalog.hasFact("Encodes.table", {"test.f1", "test.f1"}),
          "codec facts check actual payload kind and nominal domain");
  require(catalog.hasFact("Encodes.bool", {"test.bool"}) &&
              !catalog.hasFact("Encodes.bool", {"test.bool", "test.f1"}),
          "bool codec has no payload domain argument");
  require(catalog.defaultCodec("table", "test.f2")->identity == "test.codec2" &&
              !catalog.defaultCodec("table", "missing") &&
              !catalog.defaultCodec("bool", "test.f1"),
          "codec defaults use both kind and domain");
  require(catalog.defaultRepresentation("table", "test.f1")->identity ==
              "test.lsb/1",
          "explicitly installed default");
  require(
      !catalog.defaultRepresentation("table", "test.f2") &&
          !catalog.defaultRepresentation("field", "test.f1") &&
          !catalog.defaultRepresentation("table", "missing") &&
          !catalog.defaultRepresentation("unknown", "test.f1") &&
          !catalog.defaultRepresentation("bool", "test.f1"),
      "neither a legal representation nor the kind alone implies a default");
  require(catalog.representation("table", "test.f2", "test.other/1") &&
              !catalog.representation("table", "test.f1", "test.other/1") &&
              !catalog.representation("field", "test.f2", "test.other/1"),
          "legal representation is indexed by kind and domain");
  require(catalog.representationForLayout("table", "test.f1", "msb") &&
              !catalog.representationForLayout("table", "test.f2", "msb") &&
              !catalog.representationForLayout("table", "test.f1", "") &&
              !catalog.representationForLayout("table", "test.f1", "unknown"),
          "named layout selection never falls back");

  records.codecs.push_back({"test.alternate.codec", "table", "test.f1"});
  const auto ambiguous = accept(records.build());
  require(
      !ambiguous.defaultCodec("table", "test.f1") &&
          ambiguous.codec("test.codec1") &&
          ambiguous.codec("test.alternate.codec") &&
          ambiguous.defaultCodec("table", "test.f2"),
      "ambiguous codec defaults fail closed without hiding explicit codecs");
  records.reps.push_back({"test.lsb/1", "field", "test.f2", true, ""});
  records.logicalTypes.push_back({"field", "test.f2"});
  records.reps[2].identity = "test.lsb/1";
  records.reps[2].isDefault = true;
  const auto shared = accept(records.build());
  require(shared.defaultRepresentation("field", "test.f2") &&
              shared.defaultRepresentation("table", "test.f2"),
          "representation identity may serve separately installed tuples");
  records.domains.clear();
  records.codecs.clear();
  records.reps.clear();
  records.logicalTypes.clear();
  records.providers.clear();
  require(catalog.domain("test.f1") && catalog.codec("test.codec1") &&
              shared.defaultRepresentation("table", "test.f2") &&
              shared.admitsLogicalType("field", "test.f2") &&
              shared.defaultProvider("test.f1") == "custom",
          "catalog owns all nested input strings");
  const auto empty = accept(records.build());
  require(!empty.defaultCodec("bool", "") &&
              !empty.defaultRepresentation("bool", "") &&
              !empty.admitsLogicalType("bool", "") &&
              empty.defaultProvider("test.f1").empty(),
          "empty closed catalog guesses nothing, including bool");
}

void independentFormationAndProviders() {
  Records records;
  records.codecs.clear();
  records.reps.clear();
  records.providers.clear();
  records.logicalTypes = {{"field", "test.f1"}, {"field", "test.f2"}};
  const auto logical = accept(records.build());
  require(logical.admitsLogicalType("field", "test.f1") &&
              !logical.defaultRepresentation("field", "test.f1") &&
              !logical.defaultCodec("field", "test.f1") &&
              logical.defaultProvider("test.f1").empty(),
          "a declared mathematical type needs no physical realization");
  require(!logical.admitsLogicalType("table", "test.f1") &&
              !logical.admitsLogicalType("field", "test.g") &&
              !logical.admitsLogicalType("field", "missing"),
          "sort and nominal installation do not imply logical admission");

  records.reps = {
      {"dalek.unrelated-carrier/1", "field", "test.f1", true, ""},
      {"plonky3.unselected-carrier/1", "field", "test.f2", true, ""}};
  const auto physical = accept(records.build());
  require(physical.defaultProvider("test.f1").empty() &&
              physical.defaultProvider("test.f2").empty(),
          "representation names cannot create default provider policy");
  records.providers = {{"test.f1", "custom"}};
  const auto selected = accept(records.build());
  require(
      selected.defaultProvider("test.f1") == "custom" &&
          selected.defaultRepresentation("field", "test.f1")->identity ==
              "dalek.unrelated-carrier/1" &&
          selected.defaultProvider("test.f2").empty() &&
          selected.defaultProvider("test.g").empty(),
      "explicit provider policy ignores representation and associated names");
  records.reps[0].identity = "arkworks.renamed-carrier/1";
  require(accept(records.build()).defaultProvider("test.f1") == "custom",
          "renaming a representation leaves provider selection unchanged");

  records.domains.push_back(
      {"test.suite", "Transcript", {{"ChallengeField", "test.f1"}}, {}});
  records.providers.push_back({"test.suite", "unimplemented"});
  records.logicalTypes.clear();
  records.reps.clear();
  const auto policyOnly = accept(records.build());
  require(policyOnly.defaultProvider("test.suite") == "unimplemented" &&
              !policyOnly.hasFact("FieldTranscript", {"test.suite"}) &&
              !policyOnly.admitsLogicalType("transcript", "test.suite") &&
              !policyOnly.defaultRepresentation("transcript", "test.suite"),
          "provider policy registers no type, representation or capability");
}

void installedInventory() {
  // Frozen independently of representations: changing physical availability
  // must not broaden or narrow this logical formation profile.
  const std::map<std::string, std::vector<std::string>> expected{
      {"", {"bool", "index", "indices"}},
      {"bls12-381.fr",
       {"field", "vector", "polynomial", "round", "matrix", "table", "point",
        "rng", "nonce"}},
      {"ristretto255.scalar",
       {"field", "vector", "polynomial", "round", "matrix", "rng", "nonce"}},
      {"bn254.fr", {"field", "vector", "polynomial", "round", "matrix", "rng"}},
      {"koala-bear", {"field", "vector", "polynomial", "round", "matrix"}},
      {"koala-bear.ext8-binomial3",
       {"field", "vector", "polynomial", "round", "matrix", "rng"}},
      {"bls12-381.g1", {"group", "groups"}},
      {"ristretto255.group", {"group", "groups"}},
      {"bn254.g1", {"group", "groups"}},
      {"bn254.g2", {"group", "groups"}},
      {"merlin3.bls12-381.fr64be/1", {"transcript"}},
      {"spongefish0.7.4.keccak.bls12-381.fr64be/1", {"transcript"}},
      {"merlin3.ristretto255.scalar64le/1", {"transcript"}},
      {"merlin3.koala-bear.ext8-binomial3.rejection31le/1", {"transcript"}},
      {"multilinear.kzg.bls12-381/1",
       {"commitment", "proof", "prover_key", "verifier_key", "opening_state"}},
      {"rows.merkle-keccak256.koala-bear/1",
       {"commitment", "proof", "opening_state", "commitments",
        "opening_states"}},
      {"rows.merkle-keccak256.koala-bear.ext8-binomial3/1",
       {"commitment", "proof", "opening_state", "commitments",
        "opening_states"}}};
  std::set<std::pair<std::string, std::string>> pairs, actual;
  for (const auto &[domain, kinds] : expected)
    for (const auto &kind : kinds)
      pairs.emplace(kind, domain);
  const auto &catalog = installedDomains();
  for (const auto &type : catalog.allLogicalTypes())
    require(actual.emplace(type.kind, type.domain).second,
            "logical inventory contains no duplicate instances");
  require(pairs.size() == 63 && actual == pairs,
          "the complete installed logical inventory is unchanged");

  std::vector<std::string> identities{"", "missing"};
  for (const auto &domain : catalog.allDomains())
    identities.push_back(domain.identity);
  for (const auto &codec : catalog.allCodecs())
    identities.push_back(codec.identity);
  for (const auto &constructor : boundTypeConstructors()) {
    if (constructor.name == "variant" || constructor.name == "resource_unit")
      continue;
    for (const auto &identity : identities) {
      const bool admitted = pairs.count({constructor.name, identity});
      require(catalog.admitsLogicalType(constructor.name, identity) == admitted,
              "only exact declared logical pairs are admitted");
      BoundType logical{constructor.name, identity, ""};
      auto parsed = parseBoundType(logical.spelling(), false);
      if (admitted)
        require(accept(std::move(parsed)) == logical,
                "every installed logical spelling is unchanged");
      else
        refuse(std::move(parsed), "binding-type-identity");
    }
  }

  const std::map<std::string, std::string> providers{
      {"bls12-381.fr", "arkworks"},
      {"bls12-381.g1", "arkworks"},
      {"bn254.fr", "arkworks"},
      {"bn254.g1", "arkworks"},
      {"bn254.g2", "arkworks"},
      {"multilinear.kzg.bls12-381/1", "arkworks"},
      {"merlin3.bls12-381.fr64be/1", "arkworks"},
      {"ristretto255.scalar", "dalek"},
      {"ristretto255.group", "dalek"},
      {"merlin3.ristretto255.scalar64le/1", "dalek"},
      {"spongefish0.7.4.keccak.bls12-381.fr64be/1", "spongefish"},
      {"koala-bear", "plonky3"},
      {"koala-bear.ext8-binomial3", "plonky3"},
      {"merlin3.koala-bear.ext8-binomial3.rejection31le/1", "plonky3"},
      {"rows.merkle-keccak256.koala-bear/1", "plonky3"},
      {"rows.merkle-keccak256.koala-bear.ext8-binomial3/1", "plonky3"}};
  require(catalog.allDomains().size() == providers.size(),
          "the complete installed provider domain inventory is unchanged");
  for (const auto &identity : identities) {
    auto expectedProvider = providers.find(identity);
    require(catalog.defaultProvider(identity) ==
                (expectedProvider == providers.end()
                     ? StringRef{}
                     : StringRef(expectedProvider->second)),
            "all installed provider selections are unchanged");
  }
}

struct ExpectedType {
  const char *kind, *domain, *rep, *codec;
};
const ExpectedType types[] = {
    {"bool", "", "native.bool/1", "zkcv.bool/1"},
    {"index", "", "native.index/1", "zkcv.index/1"},
    {"indices", "", "native.indices/1", "zkcv.indices/1"},
    {"field", "bls12-381.fr", "arkworks.fr/1", "zkcv.field.bls12-381.fr/1"},
    {"vector", "bls12-381.fr", "arkworks.fr-vector/1",
     "zkcv.vector.bls12-381.fr/1"},
    {"matrix", "bls12-381.fr", "arkworks.fr-sparse-coo/1",
     "zkcv.matrix.bls12-381.fr/1"},
    {"polynomial", "bls12-381.fr", "arkworks.polynomial/1",
     "zkcv.polynomial.bls12-381.fr/1"},
    {"table", "bls12-381.fr", "arkworks.mle-lsb/1",
     "zkcv.table.bls12-381.fr/1"},
    {"point", "bls12-381.fr", "arkworks.point/1", "zkcv.point.bls12-381.fr/1"},
    {"round", "bls12-381.fr", "arkworks.quadratic/1",
     "zkcv.round.bls12-381.fr/1"},
    {"group", "bls12-381.g1", "arkworks.g1/1", "zkcv.group.bls12-381.g1/1"},
    {"groups", "bls12-381.g1", "arkworks.g1-vector/1",
     "zkcv.groups.bls12-381.g1/1"},
    {"rng", "bls12-381.fr", "host.resource/1", ""},
    {"nonce", "bls12-381.fr", "host.resource/1", ""},
    {"transcript", "merlin3.bls12-381.fr64be/1", "host.resource/1", ""},
    {"commitment", "multilinear.kzg.bls12-381/1", "arkworks.multilinear-pcs/1",
     "zkcv.commitment.multilinear-kzg.bls12-381/1"},
    {"proof", "multilinear.kzg.bls12-381/1", "arkworks.multilinear-pcs/1",
     "zkcv.proof.multilinear-kzg.bls12-381/1"},
    {"prover_key", "multilinear.kzg.bls12-381/1", "arkworks.multilinear-pcs/1",
     ""},
    {"verifier_key", "multilinear.kzg.bls12-381/1",
     "arkworks.multilinear-pcs/1", ""},
    {"opening_state", "multilinear.kzg.bls12-381/1",
     "arkworks.multilinear-pcs/1", ""}};

void installedBindings() {
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  const auto &catalog = installedDomains();
  std::map<std::string, std::string> codecs;
  for (const auto &t : types) {
    BoundType logical{t.kind, t.domain, ""};
    BoundType physical{t.kind, t.domain, t.rep};
    require(accept(defaultRepresentation(logical)) == physical,
            "installed default spelling is unchanged");
    require(defaultCodec(logical) == t.codec && defaultCodec(physical).empty(),
            "installed logical codec default is unchanged");
    require(catalog.representation(t.kind, t.domain, t.rep) &&
                !catalog.representation(t.kind, "unsupported", t.rep),
            "installed applicability uses complete domain identity");
    for (const auto &type : {logical, physical}) {
      bool isPhysical = !type.representation.empty();
      require(accept(parseBoundType(type.spelling(), isPhysical)) == type &&
                  accept(encodeBoundType(decodeBoundType(&context, type),
                                         isPhysical)) == type,
              "all installed logical/physical types round trip");
    }
    codecs[t.kind] = t.codec;
  }
  require(installedIdentitySort("bls12-381.fr") == "Field" &&
              installedIdentitySort("bls12-381.g1") == "Group" &&
              installedIdentitySort("multilinear.kzg.bls12-381/1") ==
                  "Commitment" &&
              installedIdentitySort("merlin3.bls12-381.fr64be/1") ==
                  "Transcript" &&
              installedIdentitySort("zkcv.bool/1") == "Codec",
          "installed nominal and codec sorts");
  for (StringRef member : {"ValueField", "PointField", "EvaluationField"})
    require(associatedIdentity("multilinear.kzg.bls12-381/1", member) ==
                "bls12-381.fr",
            "PCS associated field");
  require(associatedIdentity("bls12-381.g1", "Scalar") == "bls12-381.fr" &&
              associatedIdentity("merlin3.bls12-381.fr64be/1",
                                 "ChallengeField") == "bls12-381.fr",
          "group and transcript associated fields");
  for (StringRef fact :
       {"Field", "CommRing", "PrimeField", "CharacteristicNotTwo"})
    require(catalog.hasFact(fact, {"bls12-381.fr"}), "installed field facts");
  require(
      catalog.hasFact("Group", {"bls12-381.g1"}) &&
          catalog.hasFact("ScalarAction", {"bls12-381.g1"}) &&
          catalog.hasFact("MultilinearOpening",
                          {"multilinear.kzg.bls12-381/1"}) &&
          catalog.hasFact("FieldTranscript", {"merlin3.bls12-381.fr64be/1"}) &&
          catalog.hasFact("Transcript", {"merlin3.bls12-381.fr64be/1"}),
      "installed group, PCS and transcript facts");

  codecs["commitments"] = "zkcv.commitments.rows-merkle-keccak256.koala-bear/1";
  std::map<std::string, std::string> roots{
      {"Field", "bls12-381.fr"},
      {"Group", "bls12-381.g1"},
      {"Commitment", "multilinear.kzg.bls12-381/1"},
      {"Transcript", "merlin3.bls12-381.fr64be/1"}};
  for (const auto &operation : boundOperationContracts()) {
    const bool oracle =
        any_of(operation.signature.requirements, [](const auto &predicate) {
          return predicate.relation == "VectorCommitment";
        });
    const bool embedding =
        operation.name == "field.embed" || operation.name == "vector.embed";
    const bool twoAdic =
        any_of(operation.signature.requirements, [](const auto &predicate) {
          return predicate.relation == "TwoAdicField";
        });
    source::OperationBinding binding{{}, "test", {operation.name, {}, ""}};
    for (auto [i, term] : enumerate(operation.signature.scope.terms))
      if (!term.parent && !term.arguments &&
          !operation.signature.scope.constants.count(i)) {
        const auto &sort = operation.signature.scope.sorts[i];
        binding.application.arguments.push_back(
            sort == "Codec"
                ? codecs.at(
                      StringRef(operation.name)
                          .drop_front(StringRef("transcript.observe.").size())
                          .str())
            : sort == "Commitment" &&
                    (oracle ||
                     operation.name == "transcript.observe.commitments")
                ? "rows.merkle-keccak256.koala-bear/1"
            : sort == "Transcript" &&
                    (operation.name == "transcript.draw_index" ||
                     operation.name == "transcript.observe.commitments")
                ? "merlin3.koala-bear.ext8-binomial3.rejection31le/1"
            : sort == "Field" && (embedding || operation.name == "random.index")
                ? "koala-bear.ext8-binomial3"
            : sort == "Field" && operation.name == "pairing.check" ? "bn254.fr"
            : sort == "Nat"                                        ? "4"
            : sort == "Field" &&
                    (twoAdic ||
                     StringRef(operation.name).starts_with("fixed_vector."))
                ? "koala-bear"
                : roots.at(sort));
      }
    const auto logical = accept(resolveBinding(binding.application, false));
    const auto selected = accept(defaultImplementation(binding.application));
    const std::string defaultPrefix =
        (StringRef(selected).split('/').first + "/").str();
    for (StringRef prefix :
         {StringRef(defaultPrefix), StringRef("arkworks-msb/")}) {
      if (prefix == "arkworks-msb/" &&
          !is_contained(
              ArrayRef<StringRef>{"poly.product_sum", "poly.product_round",
                                  "poly.boundary", "poly.round_evaluate",
                                  "poly.fold", "poly.evaluate",
                                  "poly.empty_point", "poly.append_point"},
              operation.name))
        continue;
      binding.application.implementation = (prefix + operation.name).str();
      const auto physical = accept(resolveBinding(binding.application, true));
      auto compare = [&](ArrayRef<BoundType> before,
                         ArrayRef<BoundType> after) {
        require(before.size() == after.size(), "installed signature arity");
        for (auto [a, b] : zip(before, after)) {
          auto expected = a;
          expected.representation =
              prefix == "arkworks-msb/" && a.kind == "table"
                  ? "arkworks.mle-msb/1"
                  : accept(defaultRepresentation(a)).representation;
          require(b == expected,
                  "installed operation representation selection");
        }
      };
      compare(logical.inputs, physical.inputs);
      compare(logical.outputs, physical.outputs);
      const auto constrained =
          accept(resolveBinding(binding.application, false));
      require(constrained.inputs == logical.inputs &&
                  constrained.outputs == logical.outputs,
              "implementation constraints retain logical port types");
    }
  }
  refuse(defaultRepresentation({"field", "unsupported", ""}),
         "binding-type-identity");
  refuse(defaultRepresentation({"field", "bls12-381.g1", ""}),
         "binding-type-identity");
  refuse(defaultRepresentation({"unknown", "bls12-381.fr", ""}),
         "binding-type");
  refuse(defaultRepresentation({"bool", "", "native.bool/1"}),
         "binding-physical-type-at-logical-stage");
  refuse(parseBoundType("table:bls12-381.fr@arkworks.fr/1", true),
         "binding-representation");
  refuse(parseBoundType("table:unsupported@arkworks.mle-lsb/1", true),
         "binding-type-identity");

  source::OperationBinding conversion{
      {},
      "convert",
      {"table.relayout",
       {"bls12-381.fr", "arkworks.mle-lsb/1", "arkworks.mle-msb/1"},
       "arkworks/table.relayout"}};
  require(accept(resolveBinding(conversion.application, true))
                  .outputs[0]
                  .representation == "arkworks.mle-msb/1",
          "explicit table conversion");
  conversion.application.arguments[0] = "unsupported";
  refuse(resolveBinding(conversion.application, true), "binding-conversion");
  conversion.application.arguments[0] = "bls12-381.fr";
  conversion.application.arguments[1] = conversion.application.arguments[2];
  refuse(resolveBinding(conversion.application, true), "binding-conversion");
  conversion.application.arguments[1] = "missing";
  refuse(resolveBinding(conversion.application, true),
         "binding-representation");
}
} // namespace

void numericalField() {
  const auto &catalog = installedDomains();
  require(
      catalog.identitySort("koala-bear") == "Field" &&
          catalog.associatedIdentity("koala-bear", "Scalar").empty() &&
          catalog.associatedIdentity("koala-bear", "ChallengeField").empty(),
      "numerical support invents no associated cryptographic service");
  for (StringRef kind : {"field", "vector", "polynomial", "round"}) {
    const auto *codec = catalog.defaultCodec(kind, "koala-bear");
    const auto *rep = catalog.defaultRepresentation(kind, "koala-bear");
    require(codec && rep, "numerical carrier codec and representation");
    BoundType ty{kind.str(), "koala-bear", rep->identity};
    require(accept(parseBoundType(ty.spelling(), true)) == ty,
            "numerical physical type round trip");
  }
  for (StringRef kind : {"table", "point", "rng", "nonce", "group",
                         "transcript", "prover_key", "verifier_key"})
    require(!catalog.defaultRepresentation(kind, "koala-bear"),
            "field availability does not imply unrelated representations");
  source::OperationBinding dot{{}, "dot", {"vector.dot", {"koala-bear"}, ""}};
  require(accept(defaultImplementation(dot.application)) ==
              "plonky3/vector.dot",
          "numerical provider selected from the installed contract");
  dot.application.implementation = "arkworks/vector.dot";
  refuse(resolveBinding(dot.application, true), "binding-implementation");
  dot.application.arguments = {"bls12-381.fr"};
  dot.application.implementation = "plonky3/vector.dot";
  refuse(resolveBinding(dot.application, true), "binding-implementation");
}

void extensionField() {
  const std::string extension = "koala-bear.ext8-binomial3";
  const auto &catalog = installedDomains();
  require(catalog.associatedIdentity(extension, "BaseField") == "koala-bear",
          "extension base is nominal metadata");
  require(catalog.hasFact("ExtensionField", {extension}) &&
              catalog.hasFact("Field", {extension}) &&
              !catalog.hasFact("PrimeField", {extension}) &&
              !catalog.hasFact("ExtensionField", {"koala-bear"}),
          "extension capability does not imply prime field");
  require(catalog.domain(extension)->modulus == "2130706433",
          "natural embeddings use the characteristic, not cardinality");
  for (StringRef kind : {"field", "vector", "polynomial", "round", "matrix"}) {
    BoundType type{kind.str(), extension, ""};
    require(!defaultCodec(type).empty(), "extension codec installed");
    auto physical = accept(defaultRepresentation(type));
    require(accept(parseBoundType(physical.spelling(), true)) == physical,
            "extension carrier has exact physical identity");
  }
  require(catalog.defaultRepresentation("rng", extension),
          "extension randomness has an explicit resource representation");
  for (StringRef kind : {"table", "point", "nonce", "transcript", "group",
                         "prover_key", "verifier_key"})
    require(!catalog.defaultRepresentation(kind, extension),
            "no unsupported extension services");
  source::OperationBinding embed{{}, "embed", {"field.embed", {extension}, ""}};
  const auto logical = accept(resolveBinding(embed.application, false));
  require(
      logical.inputs == std::vector<BoundType>{{"field", "koala-bear", ""}} &&
          logical.outputs == std::vector<BoundType>{{"field", extension, ""}},
      "embedding signature uses the associated base");
  embed.application.implementation =
      accept(defaultImplementation(embed.application));
  require(embed.application.implementation == "plonky3/field.embed",
          "extension provider");
  require(accept(resolveBinding(embed.application, true))
                  .inputs[0]
                  .representation == "plonky3.koala-bear/1",
          "embedding has distinct physical ports");
  embed.application.arguments = {"koala-bear"};
  refuse(resolveBinding(embed.application, true), "binding-static-identity");
}

void bn254Domains() {
  const auto &catalog = installedDomains();
  require(fieldModulus("bn254.fr") == "2188824287183927522224640574525727508854"
                                      "8364400416034343698204186575808495617",
          "BN254 Fr uses the scalar modulus, not the coordinate modulus");
  require(catalog.hasFact("PairingField", {"bn254.fr"}) &&
              catalog.hasFact("TwoAdicField", {"bn254.fr"}) &&
              associatedIdentity("bn254.fr", "PairingG1") == "bn254.g1" &&
              associatedIdentity("bn254.fr", "PairingG2") == "bn254.g2",
          "pairing source groups are ordered nominal associations");
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  for (const auto &t : std::vector<ExpectedType>{
           {"field", "bn254.fr", "arkworks.bn254-fr/1",
            "zkcv.field.bn254.fr/1"},
           {"vector", "bn254.fr", "arkworks.bn254-fr-vector/1",
            "zkcv.vector.bn254.fr/1"},
           {"polynomial", "bn254.fr", "arkworks.bn254-fr-polynomial/1",
            "zkcv.polynomial.bn254.fr/1"},
           {"round", "bn254.fr", "arkworks.bn254-fr-round/1",
            "zkcv.round.bn254.fr/1"},
           {"matrix", "bn254.fr", "arkworks.bn254-fr-sparse-coo/1",
            "zkcv.matrix.bn254.fr/1"},
           {"group", "bn254.g1", "arkworks.bn254-g1/1",
            "zkcv.group.bn254.g1/1"},
           {"groups", "bn254.g1", "arkworks.bn254-g1-vector/1",
            "zkcv.groups.bn254.g1/1"},
           {"group", "bn254.g2", "arkworks.bn254-g2/1",
            "zkcv.group.bn254.g2/1"},
           {"groups", "bn254.g2", "arkworks.bn254-g2-vector/1",
            "zkcv.groups.bn254.g2/1"}}) {
    BoundType logical{t.kind, t.domain, ""};
    const auto physical = accept(defaultRepresentation(logical));
    require(physical.representation == t.rep &&
                defaultCodec(logical) == t.codec,
            "BN254 carrier has its exact representation and codec");
    for (const auto &type : {logical, physical})
      require(accept(encodeBoundType(decodeBoundType(&context, type),
                                     !type.representation.empty())) == type,
              "BN254 logical/physical MLIR type round trip");
    require(catalog.hasFact("Encodes." + logical.kind, {t.codec, t.domain}),
            "BN254 codec applies to its nominal payload");
    require(!catalog.hasFact("Encodes." + logical.kind,
                             {t.codec, logical.identity == "bn254.g2"
                                           ? "bn254.g1"
                                           : "bn254.g2"}),
            "BN254 codec cannot substitute another nominal payload");
  }
  for (StringRef group : {"bn254.g1", "bn254.g2"}) {
    require(associatedIdentity(group, "Scalar") == "bn254.fr",
            "both BN254 groups act by Fr");
    for (const auto &op : boundOperationContracts()) {
      if (!StringRef(op.name).starts_with("curve.") ||
          op.name == "curve.commit" || op.name == "curve.response")
        continue;
      source::OperationBinding binding{{}, "bn", {op.name, {group.str()}, ""}};
      binding.application.implementation =
          accept(defaultImplementation(binding.application));
      require(binding.application.implementation == "arkworks/" + op.name,
              "existing arkworks curve operation dispatches by nominal group");
      for (const auto &type :
           accept(resolveBinding(binding.application, true)).inputs)
        if (type.kind == "group" || type.kind == "groups")
          require(type.identity == group, "curve inputs keep G1/G2 identity");
    }
  }
  require(catalog.defaultRepresentation("rng", "bn254.fr"),
          "BN254 prover randomness has an explicit entropy resource");
  for (StringRef kind : {"table", "point", "nonce", "transcript"})
    require(!catalog.defaultRepresentation(kind, "bn254.fr"),
            "BN254 does not invent unrelated execution services");
  refuse(parseBoundType("groups:bn254.g1@arkworks.bn254-g2-vector/1", true),
         "binding-representation");
  refuse(parseBoundType("field:bn254.fr@arkworks.fr/1", true),
         "binding-representation");
  require(!catalog.hasFact("Encodes.field",
                           {"zkcv.field.bn254.fr/1", "bls12-381.fr"}),
          "BN254 and BLS scalar codecs remain nominally distinct");
  source::OperationBinding msb{{},
                               "round",
                               {"poly.round_evaluate",
                                {"bn254.fr"},
                                "arkworks-msb/poly.round_evaluate"}};
  refuse(resolveBinding(msb.application, true), "binding-implementation");
  source::OperationBinding pairing{
      {}, "check", {"pairing.check", {"bn254.fr"}, ""}};
  auto logical = accept(resolveBinding(pairing.application, false));
  require(boundOperationName(pairing.application.contract) ==
                  "algebra.pairing_check" &&
              logical.inputs ==
                  std::vector<BoundType>{{"groups", "bn254.g1", ""},
                                         {"groups", "bn254.g2", ""}} &&
              logical.outputs == std::vector<BoundType>{{"bool", "", ""}},
          "pairing has ordered distinct group-vector operands");
  require(accept(defaultImplementation(pairing.application)) ==
              "arkworks/pairing.check",
          "pairing uses the existing arkworks provider");
  pairing.application.implementation = "dalek/pairing.check";
  refuse(resolveBinding(pairing.application, true), "binding-implementation");
  pairing.application.implementation.clear();
  pairing.application.arguments = {"bn254.g1", "bn254.g2"};
  refuse(resolveBinding(pairing.application, false), "binding-static-identity");
  pairing.application.arguments = {"bls12-381.fr"};
  refuse(resolveBinding(pairing.application, false), "binding-static-identity");
  pairing.application.arguments.clear();
  refuse(resolveBinding(pairing.application, false), "binding-static-arity");

  for (StringRef contract :
       {"field.add", "vector.dot", "matrix.mul_vector", "poly.coset_evaluate",
        "poly.coset_interpolate", "poly.domain_root", "poly.domain_point",
        "poly.domain_points", "poly.even_odd_fold", "poly.opening_quotient",
        "poly.divide_opening", "poly.univariate_evaluate",
        "poly.round_evaluate", "random.draw", "random.vector"}) {
    source::OperationBinding binding{
        {}, "bn", {contract.str(), {"bn254.fr"}, ""}};
    require(accept(defaultImplementation(binding.application)) ==
                ("arkworks/" + contract).str(),
            "BN254 numerical contracts have installed physical carriers");
  }

  // Catalog formation itself rejects pairings with one source group aliased,
  // absent, or attached to a different scalar field.
  auto records = std::vector<NominalDomain>{
      {"f",
       "Field",
       {{"PairingG1", "g1"}, {"PairingG2", "g2"}},
       {"PairingField"}},
      {"g1", "Group", {{"Scalar", "f"}}, {"ScalarAction"}},
      {"g2", "Group", {{"Scalar", "f"}}, {"ScalarAction"}},
      {"other", "Field", {}, {"Field"}}};
  accept(DomainCatalog::create(records, {}, {}, {}));
  for (unsigned mutation = 0; mutation < 4; ++mutation) {
    auto bad = records;
    if (mutation == 0)
      bad[0].associated[1].identity = "g1";
    else if (mutation == 1)
      bad[0].associated.pop_back();
    else if (mutation == 2)
      bad[2].associated[0].identity = "other";
    else
      bad[2].capabilities.clear();
    refuse(DomainCatalog::create(bad, {}, {}, {}),
           "invalid pairing group association");
  }
}

int main() {
  malformedCatalogs();
  closedCatalogs();
  independentFormationAndProviders();
  installedInventory();
  installedBindings();
  numericalField();
  extensionField();
  bn254Domains();
  outs() << "nominal domains: " << checks << " checks passed\n";
}
