#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Bindings.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/ErrorHandling.h"
#include <set>
#include <tuple>

using namespace llvm;
namespace zkc::protocol {
namespace {
bool validName(StringRef value) {
  return !value.empty() && value.size() <= 256 &&
         (isAlpha(value.front()) || value.front() == '_') &&
         all_of(value, [](char c) {
           return isAlnum(c) || c == '_' || c == '.' || c == '-' || c == '/';
         });
}

Error invalid(StringRef reason) {
  return createStringError(inconvertibleErrorCode(), reason);
}

bool applicableType(const DomainCatalog &catalog, StringRef kind,
                    StringRef identity) {
  for (const auto &type : boundTypeConstructors())
    if (type.name == kind)
      return type.parameters.empty()
                 ? identity.empty()
                 : type.parameters.size() == 1 &&
                       catalog.identitySort(identity) == type.parameters[0];
  return false;
}

bool validPredicate(StringRef predicate, ArrayRef<std::string> sorts) {
  generic::Signature signature;
  signature.scope.sorts = sorts.vec();
  std::vector<unsigned> arguments;
  for (unsigned i = 0; i < sorts.size(); ++i)
    arguments.push_back(i);
  signature.requirements.push_back(
      requirements::Predicate::holds(predicate.str(), std::move(arguments)));
  if (auto error = checkStaticVocabulary(signature)) {
    consumeError(std::move(error));
    return false;
  }
  return true;
}
} // namespace

DomainCatalog::DomainCatalog(std::vector<NominalDomain> domains,
                             std::vector<CodecIdentity> codecs,
                             std::vector<DomainRepresentation> representations)
    : domains(std::move(domains)), codecs(std::move(codecs)),
      representations(std::move(representations)) {}

Expected<DomainCatalog>
DomainCatalog::create(std::vector<NominalDomain> domains,
                      std::vector<CodecIdentity> codecs,
                      std::vector<DomainRepresentation> representations) {
  DomainCatalog catalog(std::move(domains), std::move(codecs),
                        std::move(representations));
  std::set<std::string> identities;
  for (const auto &d : catalog.domains) {
    if (!validName(d.identity))
      return invalid("invalid catalog identity");
    if (!identities.insert(d.identity).second)
      return invalid("duplicate catalog identity");
    generic::Signature signature;
    signature.scope.sorts = {d.sort};
    if (auto error = checkStaticVocabulary(signature)) {
      consumeError(std::move(error));
      return invalid("invalid domain sort");
    }
    if (d.sort == "Codec")
      return invalid("invalid domain sort");
    if (!d.modulus.empty() &&
        (d.sort != "Field" || d.modulus.size() > 1024 ||
         d.modulus.front() == '0' || d.modulus == "1" ||
         !all_of(d.modulus, [](char c) { return isDigit(c); })))
      return invalid("invalid field modulus");
  }
  for (const auto &c : catalog.codecs) {
    if (!validName(c.identity))
      return invalid("invalid catalog identity");
    if (!identities.insert(c.identity).second)
      return invalid("duplicate catalog identity");
  }
  for (const auto &d : catalog.domains) {
    std::set<std::string> members, facts;
    for (const auto &a : d.associated) {
      if (!members.insert(a.member).second)
        return invalid("duplicate associated member");
      StringRef expected = associatedMemberSort(d.sort, a.member);
      if (expected.empty() || catalog.identitySort(a.identity) != expected)
        return invalid("invalid associated identity");
    }
    for (const auto &fact : d.capabilities) {
      if (!facts.insert(fact).second)
        return invalid("duplicate capability fact");
      if (!validPredicate(fact, {d.sort}))
        return invalid("invalid capability fact");
    }
  }
  for (const auto &c : catalog.codecs) {
    if (!applicableType(catalog, c.kind, c.domain))
      return invalid("invalid codec payload domain");
    std::vector<std::string> sorts{"Codec"};
    if (!c.domain.empty())
      sorts.push_back(catalog.identitySort(c.domain).str());
    if (!validPredicate("Encodes." + c.kind, sorts))
      return invalid("invalid codec payload kind");
  }
  // A shared scalar field does not identify a pairing's ordered source groups.
  // Validate the complete association before exposing a PairingField fact.
  for (const auto &d : catalog.domains) {
    if (!is_contained(d.capabilities, "PairingField"))
      continue;
    StringRef g1 = catalog.associatedIdentity(d.identity, "PairingG1");
    StringRef g2 = catalog.associatedIdentity(d.identity, "PairingG2");
    if (g1.empty() || g2.empty() || g1 == g2 ||
        !catalog.hasFact("ScalarAction", {g1.str()}) ||
        !catalog.hasFact("ScalarAction", {g2.str()}) ||
        catalog.associatedIdentity(g1, "Scalar") != d.identity ||
        catalog.associatedIdentity(g2, "Scalar") != d.identity)
      return invalid("invalid pairing group association");
  }
  std::set<std::tuple<std::string, std::string, std::string>> legal, layouts;
  std::set<std::pair<std::string, std::string>> defaults;
  for (const auto &r : catalog.representations) {
    if (!validName(r.identity))
      return invalid("invalid representation identity");
    if (!applicableType(catalog, r.kind, r.domain))
      return invalid("invalid representation domain");
    if (!legal.emplace(r.kind, r.domain, r.identity).second)
      return invalid("duplicate representation");
    if (r.isDefault && !defaults.emplace(r.kind, r.domain).second)
      return invalid("ambiguous representation default");
    if (!r.layout.empty()) {
      if (!validName(r.layout))
        return invalid("invalid representation layout");
      if (!layouts.emplace(r.kind, r.domain, r.layout).second)
        return invalid("ambiguous representation layout");
    }
  }
  return catalog;
}

const NominalDomain *DomainCatalog::domain(StringRef identity) const {
  for (const auto &d : domains)
    if (d.identity == identity)
      return &d;
  return nullptr;
}

const CodecIdentity *DomainCatalog::codec(StringRef identity) const {
  for (const auto &c : codecs)
    if (c.identity == identity)
      return &c;
  return nullptr;
}

StringRef DomainCatalog::identitySort(StringRef identity) const {
  if (const auto *d = domain(identity))
    return d->sort;
  return codec(identity) ? "Codec" : StringRef{};
}

StringRef DomainCatalog::associatedIdentity(StringRef identity,
                                            StringRef member) const {
  if (const auto *d = domain(identity))
    for (const auto &a : d->associated)
      if (a.member == member)
        return a.identity;
  return {};
}

bool DomainCatalog::hasFact(StringRef predicate,
                            ArrayRef<std::string> arguments) const {
  if (arguments.empty())
    return false;
  if (predicate.consume_front("Encodes.")) {
    const auto *c = codec(arguments[0]);
    return c && c->kind == predicate &&
           (c->domain.empty()
                ? arguments.size() == 1
                : arguments.size() == 2 && arguments[1] == c->domain);
  }
  if (arguments.size() != 1)
    return false;
  if (const auto *d = domain(arguments[0]))
    return is_contained(d->capabilities, predicate);
  return false;
}

const CodecIdentity *DomainCatalog::defaultCodec(StringRef kind,
                                                 StringRef identity) const {
  const CodecIdentity *selected = nullptr;
  for (const auto &c : codecs)
    if (c.kind == kind && c.domain == identity) {
      if (selected)
        return nullptr;
      selected = &c;
    }
  return selected;
}

const DomainRepresentation *
DomainCatalog::representation(StringRef kind, StringRef identity,
                              StringRef representation) const {
  for (const auto &r : representations)
    if (r.kind == kind && r.domain == identity && r.identity == representation)
      return &r;
  return nullptr;
}

const DomainRepresentation *
DomainCatalog::defaultRepresentation(StringRef kind, StringRef identity) const {
  for (const auto &r : representations)
    if (r.kind == kind && r.domain == identity && r.isDefault)
      return &r; // Construction rejects ambiguous defaults.
  return nullptr;
}

const DomainRepresentation *
DomainCatalog::representationForLayout(StringRef kind, StringRef identity,
                                       StringRef layout) const {
  if (!layout.empty())
    for (const auto &r : representations)
      if (r.kind == kind && r.domain == identity && r.layout == layout)
        return &r; // Construction rejects ambiguous named layouts.
  return nullptr;
}

const DomainCatalog &installedDomains() {
  static const DomainCatalog catalog = [] {
    const std::string field = "bls12-381.fr";
    const std::string group = "bls12-381.g1";
    const std::string bn254 = "bn254.fr";
    const std::string bn254g1 = "bn254.g1";
    const std::string bn254g2 = "bn254.g2";
    const std::string pcs = "multilinear.kzg.bls12-381/1";
    const std::string transcript = "merlin3.bls12-381.fr64be/1";
    const std::string scalar = "ristretto255.scalar";
    const std::string ristretto = "ristretto255.group";
    const std::string merlin = "merlin3.ristretto255.scalar64le/1";
    const std::string spongefish = "spongefish0.7.4.keccak.bls12-381.fr64be/1";
    const std::string koala = "koala-bear";
    const std::string extension = "koala-bear.ext8-binomial3";
    const std::string extensionTranscript =
        "merlin3.koala-bear.ext8-binomial3.rejection31le/1";
    const std::string rowBase = "rows.merkle-keccak256.koala-bear/1";
    const std::string rowExtension =
        "rows.merkle-keccak256.koala-bear.ext8-binomial3/1";
    auto result = DomainCatalog::create(
        {{extensionTranscript,
          "Transcript",
          {{"ChallengeField", extension}},
          {"FieldTranscript", "IndexTranscript", "Transcript"}},
         {rowBase, "Commitment", {{"ValueField", koala}}, {"VectorCommitment"}},
         {rowExtension,
          "Commitment",
          {{"ValueField", extension}},
          {"VectorCommitment"}},
         {extension,
          "Field",
          {{"BaseField", koala}},
          {"IndexRandomness", "ExtensionField", "TwoAdicField", "Field",
           "CommRing", "CharacteristicNotTwo"},
          "2130706433"},
         {koala,
          "Field",
          {},
          {"TwoAdicField", "Field", "CommRing", "PrimeField",
           "CharacteristicNotTwo"},
          "2130706433"},
         {bn254,
          "Field",
          {{"PairingG1", bn254g1}, {"PairingG2", bn254g2}},
          {"Field", "CommRing", "PrimeField", "CharacteristicNotTwo",
           "TwoAdicField", "PairingField"},
          "21888242871839275222246405745257275088548364400416034343698204186575"
          "808495617"},
         {bn254g1, "Group", {{"Scalar", bn254}}, {"Group", "ScalarAction"}},
         {bn254g2, "Group", {{"Scalar", bn254}}, {"Group", "ScalarAction"}},
         {field,
          "Field",
          {},
          {"Field", "CommRing", "PrimeField", "CharacteristicNotTwo"},
          "52435875175126190479447740508185965837690552500527637822603658699938"
          "581184513"},
         {scalar,
          "Field",
          {},
          {"Field", "CommRing", "PrimeField", "CharacteristicNotTwo"},
          "72370055773322622139731865630429942408571163593799076060019509382854"
          "54250989"},
         {ristretto, "Group", {{"Scalar", scalar}}, {"Group", "ScalarAction"}},
         {merlin,
          "Transcript",
          {{"ChallengeField", scalar}},
          {"FieldTranscript", "Transcript"}},
         {group, "Group", {{"Scalar", field}}, {"Group", "ScalarAction"}},
         {pcs,
          "Commitment",
          {{"ValueField", field},
           {"PointField", field},
           {"EvaluationField", field}},
          {"MultilinearOpening"}},
         {spongefish,
          "Transcript",
          {{"ChallengeField", field}},
          {"FieldTranscript", "Transcript"}},
         {transcript,
          "Transcript",
          {{"ChallengeField", field}},
          {"FieldTranscript", "Transcript"}}},
        {{"zkcv.commitment.rows-merkle-keccak256.koala-bear/1", "commitment",
          rowBase},
         {"zkcv.proof.rows-merkle-keccak256.koala-bear/1", "proof", rowBase},
         {"zkcv.commitments.rows-merkle-keccak256.koala-bear/1", "commitments",
          rowBase},
         {"zkcv.commitment.rows-merkle-keccak256.koala-bear.ext8-binomial3/1",
          "commitment", rowExtension},
         {"zkcv.proof.rows-merkle-keccak256.koala-bear.ext8-binomial3/1",
          "proof", rowExtension},
         {"zkcv.commitments.rows-merkle-keccak256.koala-bear.ext8-binomial3/1",
          "commitments", rowExtension},
         {"zkcv.field.koala-bear.ext8-binomial3/1", "field", extension},
         {"zkcv.vector.koala-bear.ext8-binomial3/1", "vector", extension},
         {"zkcv.polynomial.koala-bear.ext8-binomial3/1", "polynomial",
          extension},
         {"zkcv.round.koala-bear.ext8-binomial3/1", "round", extension},
         {"zkcv.matrix.koala-bear.ext8-binomial3/1", "matrix", extension},
         {"zkcv.field.bn254.fr/1", "field", bn254},
         {"zkcv.vector.bn254.fr/1", "vector", bn254},
         {"zkcv.polynomial.bn254.fr/1", "polynomial", bn254},
         {"zkcv.round.bn254.fr/1", "round", bn254},
         {"zkcv.matrix.bn254.fr/1", "matrix", bn254},
         {"zkcv.group.bn254.g1/1", "group", bn254g1},
         {"zkcv.groups.bn254.g1/1", "groups", bn254g1},
         {"zkcv.group.bn254.g2/1", "group", bn254g2},
         {"zkcv.groups.bn254.g2/1", "groups", bn254g2},
         {"zkcv.matrix.bls12-381.fr/1", "matrix", field},
         {"zkcv.matrix.ristretto255.scalar/1", "matrix", scalar},
         {"zkcv.matrix.koala-bear/1", "matrix", koala},
         {"zkcv.field.koala-bear/1", "field", koala},
         {"zkcv.vector.koala-bear/1", "vector", koala},
         {"zkcv.polynomial.koala-bear/1", "polynomial", koala},
         {"zkcv.round.koala-bear/1", "round", koala},
         {"zkcv.vector.bls12-381.fr/1", "vector", field},
         {"zkcv.polynomial.bls12-381.fr/1", "polynomial", field},
         {"zkcv.field.ristretto255.scalar/1", "field", scalar},
         {"zkcv.vector.ristretto255.scalar/1", "vector", scalar},
         {"zkcv.polynomial.ristretto255.scalar/1", "polynomial", scalar},
         {"zkcv.round.ristretto255.scalar/1", "round", scalar},
         {"zkcv.group.ristretto255.group/1", "group", ristretto},
         {"zkcv.groups.ristretto255.group/1", "groups", ristretto},
         {"zkcv.bool/1", "bool", ""},
         {"zkcv.index/1", "index", ""},
         {"zkcv.indices/1", "indices", ""},
         {"zkcv.field.bls12-381.fr/1", "field", field},
         {"zkcv.table.bls12-381.fr/1", "table", field},
         {"zkcv.point.bls12-381.fr/1", "point", field},
         {"zkcv.round.bls12-381.fr/1", "round", field},
         {"zkcv.group.bls12-381.g1/1", "group", group},
         {"zkcv.groups.bls12-381.g1/1", "groups", group},
         {"zkcv.commitment.multilinear-kzg.bls12-381/1", "commitment", pcs},
         {"zkcv.proof.multilinear-kzg.bls12-381/1", "proof", pcs}},
        {{"plonky3.merkle-root/1", "commitment", rowBase, true, ""},
         {"plonky3.merkle-path/1", "proof", rowBase, true, ""},
         {"plonky3.merkle-state/1", "opening_state", rowBase, true, ""},
         {"plonky3.merkle-roots/1", "commitments", rowBase, true, ""},
         {"plonky3.merkle-states/1", "opening_states", rowBase, true, ""},
         {"plonky3.merkle-root/1", "commitment", rowExtension, true, ""},
         {"plonky3.merkle-path/1", "proof", rowExtension, true, ""},
         {"plonky3.merkle-state/1", "opening_state", rowExtension, true, ""},
         {"plonky3.merkle-roots/1", "commitments", rowExtension, true, ""},
         {"plonky3.merkle-states/1", "opening_states", rowExtension, true, ""},
         {"plonky3.koala-bear.ext8-binomial3/1", "field", extension, true, ""},
         {"plonky3.koala-bear.ext8-binomial3-vector/1", "vector", extension,
          true, ""},
         {"plonky3.koala-bear.ext8-binomial3-polynomial/1", "polynomial",
          extension, true, ""},
         {"plonky3.koala-bear.ext8-binomial3-quadratic/1", "round", extension,
          true, ""},
         {"plonky3.koala-bear.ext8-binomial3-sparse-coo/1", "matrix", extension,
          true, ""},
         {"arkworks.bn254-fr/1", "field", bn254, true, ""},
         {"arkworks.bn254-fr-vector/1", "vector", bn254, true, ""},
         {"arkworks.bn254-fr-polynomial/1", "polynomial", bn254, true, ""},
         {"arkworks.bn254-fr-round/1", "round", bn254, true, ""},
         {"arkworks.bn254-fr-sparse-coo/1", "matrix", bn254, true, ""},
         {"arkworks.bn254-g1/1", "group", bn254g1, true, ""},
         {"arkworks.bn254-g1-vector/1", "groups", bn254g1, true, ""},
         {"arkworks.bn254-g2/1", "group", bn254g2, true, ""},
         {"arkworks.bn254-g2-vector/1", "groups", bn254g2, true, ""},
         {"host.resource/1", "rng", bn254, true, ""},
         {"arkworks.fr-sparse-coo/1", "matrix", field, true, ""},
         {"dalek.scalar-sparse-coo/1", "matrix", scalar, true, ""},
         {"plonky3.koala-bear-sparse-coo/1", "matrix", koala, true, ""},
         {"plonky3.koala-bear/1", "field", koala, true, ""},
         {"plonky3.koala-bear-vector/1", "vector", koala, true, ""},
         {"plonky3.koala-bear-polynomial/1", "polynomial", koala, true, ""},
         {"plonky3.koala-bear-quadratic/1", "round", koala, true, ""},
         {"arkworks.fr-vector/1", "vector", field, true, ""},
         {"arkworks.polynomial/1", "polynomial", field, true, ""},
         {"dalek.scalar/1", "field", scalar, true, ""},
         {"dalek.scalar-vector/1", "vector", scalar, true, ""},
         {"dalek.polynomial/1", "polynomial", scalar, true, ""},
         {"dalek.quadratic/1", "round", scalar, true, ""},
         {"dalek.ristretto/1", "group", ristretto, true, ""},
         {"dalek.ristretto-vector/1", "groups", ristretto, true, ""},
         {"host.resource/1", "rng", scalar, true, ""},
         {"host.resource/1", "nonce", scalar, true, ""},
         {"host.resource/1", "transcript", merlin, true, ""},
         {"host.resource/1", "transcript", extensionTranscript, true, ""},
         {"host.resource/1", "rng", extension, true, ""},
         {"arkworks.fr-diagonal/1", "vector", field, false, "diagonal"},
         {"dalek.ristretto-diagonal/1", "groups", ristretto, false, "diagonal"},
         {"native.bool/1", "bool", "", true, ""},
         {"native.index/1", "index", "", true, ""},
         {"native.indices/1", "indices", "", true, ""},
         {"arkworks.fr/1", "field", field, true, ""},
         {"arkworks.mle-lsb/1", "table", field, true, "lsb"},
         {"arkworks.mle-msb/1", "table", field, false, "msb"},
         {"arkworks.point/1", "point", field, true, ""},
         {"arkworks.quadratic/1", "round", field, true, ""},
         {"arkworks.g1/1", "group", group, true, ""},
         {"arkworks.g1-vector/1", "groups", group, true, ""},
         {"host.resource/1", "rng", field, true, ""},
         {"host.resource/1", "nonce", field, true, ""},
         {"host.resource/1", "transcript", transcript, true, ""},
         {"host.resource/1", "transcript", spongefish, true, ""},
         {"arkworks.multilinear-pcs/1", "commitment", pcs, true, ""},
         {"arkworks.multilinear-pcs/1", "proof", pcs, true, ""},
         {"arkworks.multilinear-pcs/1", "prover_key", pcs, true, ""},
         {"arkworks.multilinear-pcs/1", "verifier_key", pcs, true, ""},
         {"arkworks.multilinear-pcs/1", "opening_state", pcs, true, ""}});
    if (!result)
      report_fatal_error(Twine("invalid installed domain catalog: ") +
                             toString(result.takeError()),
                         false);
    return std::move(*result);
  }();
  return catalog;
}
} // namespace zkc::protocol
