#include "support/NativeCases.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Implementations.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Contracts/TypeProperties.h"
#include "llvm/ADT/APInt.h"
#include <utility>

using namespace llvm;
using namespace zkc::protocol;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;

namespace {
// Independent expected installation, including roots from Plonky3 0.8.0.
struct Field {
  StringRef identity, base, modulus, root, maximum;
  unsigned degree, nonresidue, bytes, log;
  bool montgomery;
};
constexpr Field fields[] = {
    {"baby-bear", "baby-bear", "2013265921", "440564289", "2013265920", 1, 0, 4,
     27, true},
    {"baby-bear.ext4-binomial11", "baby-bear", "2013265921", "440564289",
     "2013265920", 4, 11, 4, 27, true},
    {"goldilocks", "goldilocks", "18446744069414584321", "1753635133440165772",
     "18446744069414584320", 1, 0, 8, 32, false},
    {"goldilocks.ext2-binomial7", "goldilocks", "18446744069414584321",
     "1753635133440165772", "18446744069414584320", 2, 7, 8, 32, false}};

Expected<BoundOperation> nativeBinding(BindingApplication binding) {
  auto implementation = defaultImplementation(binding);
  if (!implementation)
    return implementation.takeError();
  binding.implementation = std::move(*implementation);
  return resolveBinding(binding, true);
}

void installation(const Field &field) {
  const auto &catalog = installedDomains();
  const auto *entry = plonky3Field(field.identity);
  require(entry && entry->base == field.base &&
              entry->modulus == field.modulus &&
              entry->degree == field.degree &&
              entry->nonresidue == field.nonresidue &&
              entry->coordinateBytes == field.bytes &&
              entry->montgomery32 == field.montgomery,
          "registered presentation");
  require(catalog.hasFact("Field", {field.identity.str()}) &&
              catalog.hasFact("CommRing", {field.identity.str()}) &&
              catalog.hasFact("TwoAdicField", {field.identity.str()}) &&
              catalog.hasFact("CharacteristicNotTwo", {field.identity.str()}),
          "exact arithmetic capabilities");
  require(catalog.hasFact("PrimeField", {field.identity.str()}) ==
                  (field.degree == 1) &&
              catalog.hasFact("ExtensionField", {field.identity.str()}) ==
                  (field.degree > 1) &&
              catalog.hasFact("IndexRandomness", {field.identity.str()}) ==
                  (field.degree > 1) &&
              catalog.associatedIdentity(field.identity, "BaseField") ==
                  (field.degree == 1 ? StringRef{} : field.base),
          "exact base association and separately installed randomness");
  require(fieldModulus(field.identity) == field.modulus &&
              catalog.defaultProvider(field.identity) == "plonky3" &&
              implementationProviderSupports("plonky3", field.identity) &&
              !implementationProviderSupports("arkworks", field.identity),
          "characteristic and provider");
  const std::pair<StringRef, StringRef> kinds[] = {
      {"field", ""},
      {"vector", "-vector"},
      {"polynomial", "-polynomial"},
      {"round", "-quadratic"},
      {"matrix", "-sparse-coo"}};
  for (auto [kind, suffix] : kinds) {
    auto logical =
        take(parseBoundType((kind + ":" + field.identity).str(), false));
    auto physical = take(defaultRepresentation(logical));
    require(physical.representation ==
                ("plonky3." + field.identity + suffix + "/0").str(),
            "physical owner");
    const auto *codec = catalog.defaultCodec(kind, field.identity);
    require(codec && codec->identity ==
                         ("zkcv." + kind + "." + field.identity + "/0").str(),
            "exact logical codec");
    bool wire = kind == "field" || kind == "vector" || kind == "matrix";
    require(nativeMessageData(logical) == wire &&
                nativeMessageData(physical) == wire,
            "only scalar, vector and matrix have native frames");
  }
  if (auto error = checkParameters("field.constant", {field.maximum.str()},
                                   field.identity))
    throw std::runtime_error(toString(std::move(error)));
  if (auto error = checkParameters("vector.constant",
                                   {"0", field.maximum.str()}, field.identity))
    throw std::runtime_error(toString(std::move(error)));
  auto bad =
      checkParameters("field.constant", {field.modulus.str()}, field.identity);
  require(bool(bad), "modulus literal refuses");
  require(toString(std::move(bad)).find("interactive-constant") !=
              std::string::npos,
          "literal diagnostic");
  for (StringRef contract :
       {"field.constant", "vector.dot", "matrix.mul_vector",
        "poly.coset_evaluate", "ring.point", "ring.coefficients",
        "relation.table_point", "relation.table_record_points"}) {
    std::vector<std::string> arguments{field.identity.str()};
    if (contract.starts_with("relation."))
      arguments.push_back("0");
    auto operation = take(nativeBinding({contract.str(), arguments, ""}));
    require(!operation.outputs.empty(), "shared implementation is selected");
  }
  for (StringRef contract :
       {"encoding.field_montgomery_le", "encoding.field_from_montgomery_le",
        "encoding.fields_montgomery_le",
        "encoding.fields_from_montgomery_le"}) {
    auto operation =
        nativeBinding({contract.str(), {field.identity.str()}, ""});
    if (field.montgomery)
      (void)take(std::move(operation));
    else
      refuses(std::move(operation), "binding-implementation");
  }
  // A scalar Poseidon operation remains specific to its existing parameters.
  refuses(nativeBinding({"hash.poseidon2_16", {field.identity.str()}, ""}),
          "binding-implementation");
  for (StringRef kind : {"table", "point", "nonce"})
    refuses(parseBoundType((kind + ":" + field.identity).str(), false),
            "binding-type-identity");
  if (field.degree == 1)
    refuses(parseBoundType(("rng:" + field.identity).str(), false),
            "binding-type-identity");
  else {
    auto rng = take(defaultRepresentation(
        take(parseBoundType(("rng:" + field.identity).str(), false))));
    require(rng.representation == "host.resource/0",
            "explicit extension random service");
    auto contract = randomServiceContract(field.identity);
    require(
        !contract.empty() && randomServiceField(contract) == field.identity &&
            serviceMethod(contract, "draw") && serviceMethod(contract, "index"),
        "explicit draw and index service methods");
    auto suite = field.bytes == 4
                     ? "merlin3.baby-bear.ext4-binomial11.rejection31le/0"
                     : "merlin3.goldilocks.ext2-binomial7.rejection64le/0";
    require(nativeChallengeField(suite) == field.identity &&
                catalog.hasFact("Transcript", {suite}) &&
                catalog.hasFact("FieldTranscript", {suite}) &&
                catalog.hasFact("IndexTranscript", {suite}),
            "explicit Merlin challenge field");
    (void)take(
        nativeBinding({"transcript.native.indexed.challenge", {suite}, ""}));
    (void)take(nativeBinding({"transcript.native.indexed.index", {suite}, ""}));
    (void)take(nativeBinding({"transcript.native.indexed.observe.data",
                              {suite, "field:" + field.identity.str()},
                              ""}));
  }
}

void roots(const Field &field) {
  const auto *convention = cosetConvention(field.identity);
  require(convention && convention == cosetConvention(field.base) &&
              convention->rootField == field.base &&
              convention->maxLogSize == field.log &&
              convention->maximalRoot == field.root,
          "extensions use the base convention at the base limit");
  // Sufficient width for a Goldilocks product without u64 truncation.
  APInt p(128, field.modulus, 10), r(128, field.root, 10);
  for (unsigned i = 0; i + 1 < field.log; ++i)
    r = (r * r).urem(p);
  require(r == p - 1 && (r * r).urem(p) == 1, "maximal root has exact order");
}
} // namespace

int main() {
  zkc::test::Cases cases;
  for (const auto &field : fields) {
    cases.run(field.identity + " installation", [&] { installation(field); });
    cases.run(field.identity + " cosets", [&] { roots(field); });
  }
  cases.run("closed family", [] {
    require(plonky3Fields().size() == 7 &&
                !plonky3Field("baby-bear.ext4-binomial3") &&
                !plonky3Field("gf2-64.pentanomial-4-3-1") &&
                !cosetConvention("gf2-64.pentanomial-4-3-1"),
            "unknown presentations stay closed");
    refuses(parseBoundType("field:goldilocks@plonky3.baby-bear/0", true),
            "binding-representation");
    refuses(parseBoundType("field:baby-bear.ext4-binomial11@plonky3.koala-bear."
                           "ext4-binomial3/0",
                           true),
            "binding-representation");
  });
  return cases.result();
}
