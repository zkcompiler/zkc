#include "zkc/Contracts/Implementations.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Numerical.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/ResourceUnit.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/ErrorHandling.h"
#include <set>
#include <tuple>

using namespace llvm;
namespace zkc::protocol {
namespace {
using Compatibility = ImplementationDescriptor::Compatibility;

// Applicability is deliberately independent of DefaultProvider in Domains.
// Changing a preference cannot grant a backend a new nominal domain.
struct ProviderDomain {
  StringRef provider, domain;
};
constexpr ProviderDomain providerDomains[] = {
    {"arkworks", "bls12-381.fr"},
    {"arkworks", "bls12-381.g1"},
    {"arkworks", "bls12-381.g2"},
    {"arkworks", "bls12-381.gt"},
    {"halo2curves-axiom", "bn254.fr"},
    {"halo2curves-axiom", "bn254.g1"},
    {"halo2curves-axiom", "bn254.g2"},
    {"blst", "bls12-381.fr"},
    {"blst", "bls12-381.g1"},
    {"blst", "bls12-381.g2"},
    {"arkworks", "bn254.fr"},
    {"arkworks", "bn254.g1"},
    {"arkworks", "bn254.g2"},
    {"arkworks", "bn254.gt"},
    {"arkworks", "multilinear.kzg.bls12-381/0"},
    {"arkworks", "merlin3.bls12-381.fr64be/0"},
    {"arkworks", "hash-chain.keccak256.bls12-381.fr64be/0"},
    {"dalek", "ristretto255.scalar"},
    {"dalek", "ristretto255.group"},
    {"dalek", "edwards25519.prime"},
    {"dalek", "merlin3.ristretto255.scalar64le/0"},
    {"plonky3", "merlin3.koala-bear.ext8-binomial3.rejection31le/0"},
    {"plonky3", "merlin3.baby-bear.ext4-binomial11.rejection31le/0"},
    {"plonky3", "merlin3.goldilocks.ext2-binomial7.rejection64le/0"},
    {"plonky3",
     "hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0"},
    {"plonky3", "rows.merkle-keccak256.koala-bear/0"},
    {"plonky3", "rows.merkle-keccak256.koala-bear.ext8-binomial3/0"},
    {"plonky3", "rows.merkle-poseidon2-16.koala-bear/0"},
    {"plonky3", "rows.merkle-poseidon2-16.baby-bear/0"},
    {"plonky3", "rows.merkle-poseidon2-16.baby-bear.ext4-binomial11/0"},
    {"plonky3", "rows.merkle-poseidon2-8.goldilocks/0"},
    {"plonky3", "rows.merkle-poseidon2-8.goldilocks.ext2-binomial7/0"},

    {"plonky3", "rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0"},
    {"plonky3", "gf2-64.pentanomial-4-3-1"},
    {"plonky3", "gf2-64.pentanomial-4-3-1.ext3-trinomial1"},
    {"spongefish", "spongefish0.8.0.keccak.bls12-381.fr64be/0"}};

// Residue arithmetic, canonical bytes and Montgomery words have distinct
// applicability. Binary fields share canonical little-endian byte operations
// but cannot inherit residue arithmetic; Goldilocks has no Montgomery32 form.
enum class FieldSet { None, Residue, LittleEndian, Montgomery32 };

// These finite rows are the implementation inventory, not a walk over logical
// declarations. Adding a declaration grants no implementation. Provider sets
// abbreviate only the exact rows below; ports and nominal checks still apply.
enum Provider : unsigned {
  Arkworks = 1,
  Dalek = 2,
  Plonky3 = 4,
  Spongefish = 8,
  Native = 16,
  Arithmetic = Arkworks | Dalek | Plonky3
};
struct ContractRow {
  StringRef contract;
  unsigned providers;
  Compatibility compatibility = Compatibility::Nominal;
  StringRef domain = {};
  FieldSet fields = FieldSet::None;
};
constexpr auto Nominal = Compatibility::Nominal;
constexpr ContractRow contractRows[] = {
    {"ring.point", Plonky3, Nominal, {}, FieldSet::Residue},
    {"ring.rows", Plonky3, Nominal, {}, FieldSet::Residue},
    {"ring.coefficients", Plonky3, Nominal, {}, FieldSet::Residue},
    {"ring.affine_sum", Plonky3, Nominal, {}, FieldSet::Residue},
    {"relation.table_rows", Plonky3, Nominal, {}, FieldSet::Residue},
    {"relation.table_shape", Plonky3, Nominal, {}, FieldSet::Residue},
    {"relation.table_input", Plonky3, Nominal, {}, FieldSet::Residue},
    {"relation.table_scope", Plonky3, Nominal, {}, FieldSet::Residue},
    {"relation.table_point", Plonky3, Nominal, {}, FieldSet::Residue},
    {"relation.table_points", Plonky3, Nominal, {}, FieldSet::Residue},
    {"relation.table_widths", Plonky3, Nominal, {}, FieldSet::Residue},
    {"relation.table_policy", Plonky3, Nominal, {}, FieldSet::Residue},
    {"relation.table_interactions", Plonky3, Nominal, {}, FieldSet::Residue},
    {"relation.table_interaction", Plonky3, Nominal, {}, FieldSet::Residue},
    {"relation.table_record_points", Plonky3, Nominal, {}, FieldSet::Residue},
    {"sequence.empty", Native, Compatibility::Independent},
    {"sequence.append", Native, Compatibility::Independent},
    {"sequence.length", Native, Compatibility::Independent},
    {"sequence.at", Native, Compatibility::Independent},
    {"bool.and", Arkworks, Compatibility::Independent},
    {"bool.not", Arkworks, Compatibility::Independent},
    {"bool.or", Arkworks, Compatibility::Independent},
    {"control.require", Arkworks, Compatibility::Independent},
    {"index.constant", Native, Compatibility::Independent},
    {"index.add", Native, Compatibility::Independent},
    {"index.sub", Native, Compatibility::Independent},
    {"index.mul", Native, Compatibility::Independent},
    {"index.div", Native, Compatibility::Independent},
    {"index.mod", Native, Compatibility::Independent},
    {"index.equal", Native, Compatibility::Independent},
    {"index.less", Native, Compatibility::Independent},
    {"encoding.index_uleb128", Native, Compatibility::Independent},
    {"encoding.fields_be", Arkworks, Compatibility::Nominal, "bls12-381.fr"},
    {"encoding.fields_from_be", Arkworks, Compatibility::Nominal,
     "bls12-381.fr"},
    {"encoding.fields_le", Dalek, Compatibility::Nominal,
     "ristretto255.scalar"},
    {"encoding.groups_compressed", Arkworks, Compatibility::Nominal,
     "bls12-381.g1"},
    {"encoding.groups_compressed", Dalek, Compatibility::Nominal,
     "edwards25519.prime"},
    {"encoding.field_be", Arkworks, Compatibility::Nominal, "bls12-381.fr"},
    {"encoding.field_from_be", Arkworks, Compatibility::Nominal,
     "bls12-381.fr"},
    {"encoding.field_reduce_be", Arkworks, Compatibility::Nominal,
     "bls12-381.fr"},
    {"encoding.group_compressed", Arkworks, Compatibility::Nominal,
     "bls12-381.g1"},
    {"encoding.group_compressed", Arkworks, Compatibility::Nominal,
     "bls12-381.g2"},
    {"encoding.group_from_compressed", Arkworks, Compatibility::Nominal,
     "bls12-381.g1"},
    {"encoding.group_from_compressed", Arkworks, Compatibility::Nominal,
     "bls12-381.g2"},
    {"encoding.field_le", Dalek, Compatibility::Nominal, "ristretto255.scalar"},
    {"encoding.field_from_le", Dalek, Compatibility::Nominal,
     "ristretto255.scalar"},
    {"encoding.field_reduce_le", Dalek, Compatibility::Nominal,
     "ristretto255.scalar"},
    {"encoding.group_compressed", Dalek, Compatibility::Nominal,
     "edwards25519.prime"},
    {"encoding.group_from_compressed", Dalek, Compatibility::Nominal,
     "edwards25519.prime"},
    {"encoding.group_decode_cofactor", Dalek, Compatibility::Nominal,
     "edwards25519.prime"},
    {"encoding.cryptonote_map", Dalek, Compatibility::Nominal,
     "edwards25519.prime"},
    // Registered residue fields: four- or eight-byte words per coordinate.
    // Binary fields: little-endian bit patterns, with no Montgomery form.
    {"encoding.field_le", Plonky3, Nominal, {}, FieldSet::LittleEndian},
    {"encoding.field_from_le", Plonky3, Nominal, {}, FieldSet::LittleEndian},
    {"encoding.fields_le", Plonky3, Nominal, {}, FieldSet::LittleEndian},
    {"encoding.fields_from_le", Plonky3, Nominal, {}, FieldSet::LittleEndian},
    {"encoding.field_montgomery_le",
     Plonky3,
     Nominal,
     {},
     FieldSet::Montgomery32},
    {"encoding.field_from_montgomery_le",
     Plonky3,
     Nominal,
     {},
     FieldSet::Montgomery32},
    {"encoding.fields_montgomery_le",
     Plonky3,
     Nominal,
     {},
     FieldSet::Montgomery32},
    {"encoding.fields_from_montgomery_le",
     Plonky3,
     Nominal,
     {},
     FieldSet::Montgomery32},
    {"hash.keccak256", Native, Compatibility::Independent},
    {"hash.sha256", Native, Compatibility::Independent},
    {"hash.poseidon2_16", Plonky3, Compatibility::Nominal, "koala-bear"},
    {"shake128.init", Native, Compatibility::Independent},
    {"shake128.absorb", Native, Compatibility::Independent},
    {"shake128.squeeze", Native, Compatibility::Independent},
    {"bytes.repeat", Native, Compatibility::Independent},
    {"bytes.join", Native, Compatibility::Independent},
    {"bytes.empty", Native, Compatibility::Independent},
    {"bytes.append", Native, Compatibility::Independent},
    {"bytes.concat", Native, Compatibility::Independent},
    {"bytes.slice", Native, Compatibility::Independent},
    {"bytes.at", Native, Compatibility::Independent},
    {"bytes.length", Native, Compatibility::Independent},
    {"bytes.equal", Native, Compatibility::Independent},
    {"indices.empty", Native, Compatibility::Independent},
    {"indices.append", Native, Compatibility::Independent},
    {"indices.at", Native, Compatibility::Independent},
    {"indices.length", Native, Compatibility::Independent},
    {"external.monero.init", Native, Compatibility::Independent},
    {"external.monero.hash", Native, Compatibility::Independent},
    {"external.monero.update", Native, Compatibility::Independent},
    {"external.openvm.init", Native, Compatibility::Independent},
    {"external.openvm.observe", Native, Compatibility::Independent},
    {"external.openvm.sample", Native, Compatibility::Independent},
    {"external.openvm.sample_ext", Native, Compatibility::Independent},
    {"external.openvm.sample_bits", Native, Compatibility::Independent},
    {"external.openvm.check_witness", Native, Compatibility::Independent},
    {"numerical.map", Arithmetic},
    {"numerical.sum", Arithmetic},
    {"numerical.product", Arithmetic},
    {"field.constant", Arithmetic},
    {"field.from_index", Arithmetic},
    {"field.add", Arithmetic},
    {"field.sub", Arithmetic},
    {"field.neg", Arithmetic},
    {"field.mul", Arithmetic},
    {"field.inverse", Arithmetic},
    {"field.equal", Arithmetic},
    {"field.embed", Plonky3},
    {"vector.get", Arithmetic},
    {"vector.slice", Arithmetic},
    {"vector.transpose", Arithmetic},
    {"vector.length", Arithmetic},
    {"vector.rotate", Arithmetic},
    {"vector.bit_reverse", Arithmetic},
    {"vector.bit_reverse_rows", Arithmetic},
    {"vector.interleave", Arithmetic},
    {"vector.prefix_product", Arithmetic},
    {"vector.prefix_sum", Arithmetic},
    {"vector.inverse", Arithmetic},
    {"vector.embed", Plonky3},
    {"vector.fill", Arithmetic},
    {"vector.geometric", Arithmetic},
    {"vector.constant", Arithmetic},
    {"vector.scatter_sum", Arithmetic},
    {"vector.empty", Arithmetic},
    {"vector.append", Arithmetic},
    {"vector.splat", Arithmetic},
    {"vector.powers", Arithmetic},
    {"vector.equal", Arithmetic},
    {"vector.find_last", Arithmetic},
    {"vector.add", Arithmetic},
    {"vector.sub", Arithmetic},
    {"vector.mul", Arithmetic},
    {"vector.dot", Arithmetic},
    {"vector.concat", Arithmetic},
    {"vector.kronecker", Arithmetic},
    {"vector.matvec", Arithmetic},
    {"vector.scale", Arithmetic},
    {"vector.sum", Arithmetic},
    {"vector.product", Arithmetic},
    {"vector.split", Arithmetic},
    {"vector.at", Arithmetic},
    {"vector.length_check", Arithmetic},
    {"vector.gather", Arithmetic},
    {"vector.from_point", Arkworks},
    {"vector.to_point", Arkworks},
    {"vector.from_table", Arkworks},
    {"vector.to_table", Arkworks},
    {"matrix.mul_vector", Arithmetic},
    {"matrix.transpose_mul_vector", Arithmetic},
    {"matrix.bilinear", Arithmetic},
    {"matrix.dimension", Arithmetic},
    {"matrix.get", Arithmetic},
    {"matrix.row_dot", Arithmetic},
    {"matrix.column_dot", Arithmetic},
    {"matrix.shape_check", Arithmetic},
    {"matrix.identity_check", Arithmetic},
    {"poly.coefficient_count", Arithmetic},
    {"poly.coset_evaluate", Arkworks | Plonky3},
    {"poly.coset_evaluate_batch", Arkworks | Plonky3},
    {"poly.coset_extend", Arkworks | Plonky3},
    {"poly.coset_evaluate_at", Arkworks | Plonky3},
    {"poly.coset_interpolate", Arkworks | Plonky3},
    {"poly.domain_point", Arkworks | Plonky3},
    {"poly.domain_root", Arkworks | Plonky3},
    {"poly.domain_points", Arkworks | Plonky3},
    {"poly.even_odd_fold", Arkworks | Plonky3},
    {"poly.opening_quotient", Arkworks | Plonky3},
    {"poly.opening_quotient_sum", Arkworks | Plonky3},
    {"poly.divide_opening", Arithmetic},
    {"poly.equality_weights", Arkworks},
    {"poly.from_coefficients", Arithmetic},
    {"poly.coefficients", Arithmetic},
    {"poly.degree_check", Arithmetic},
    {"poly.univariate_evaluate", Arithmetic},
    {"poly.univariate_boundary", Arithmetic},
    {"poly.product_sum", Arkworks},
    {"poly.product_round", Arkworks},
    {"poly.table_arity", Arkworks},
    {"poly.boundary", Arithmetic},
    {"poly.round_evaluate", Arithmetic},
    {"poly.fold", Arkworks},
    {"poly.evaluate", Arkworks},
    {"poly.empty_point", Arkworks},
    {"poly.append_point", Arkworks},
    {"curve.neg", Arkworks | Dalek},
    {"curve.nonidentity", Arkworks | Dalek},
    {"curve.msm", Arkworks | Dalek},
    {"curve.scale_each", Arkworks | Dalek},
    {"curve.vector_add", Arkworks | Dalek},
    {"curve.vector_scale", Arkworks | Dalek},
    {"curve.split", Arkworks | Dalek},
    {"curve.concat", Arkworks | Dalek},
    {"curve.generator", Arkworks | Dalek},
    {"curve.identity", Arkworks | Dalek},
    {"curve.add", Arkworks | Dalek},
    {"curve.scale", Arkworks | Dalek},
    {"curve.equal", Arkworks | Dalek},
    {"curve.empty", Arkworks | Dalek},
    {"curve.append", Arkworks | Dalek},
    {"curve.at", Arkworks | Dalek},
    {"curve.get", Arkworks | Dalek},
    {"curve.length", Arkworks | Dalek},
    {"curve.commit", Arkworks | Dalek},
    {"curve.response", Arkworks | Dalek},
    {"pairing.check", Arkworks},
    {"pairing.apply", Arkworks},
    {"pcs.commit", Arkworks},
    {"pcs.open", Arkworks},
    {"pcs.check", Arkworks},
    {"pcs.equal", Arkworks},
    {"oracle.commit", Plonky3},
    {"oracle.open", Plonky3},
    {"oracle.check", Plonky3},
    {"oracle.open_many", Plonky3},
    {"oracle.check_many", Plonky3},
    {"commitments.empty", Plonky3},
    {"commitments.append", Plonky3},
    {"commitments.at", Plonky3},
    {"commitments.length", Plonky3},
    {"opening_states.empty", Plonky3},
    {"opening_states.append", Plonky3},
    {"opening_states.at", Plonky3},
    {"opening_states.length", Plonky3},
    {"random.vector", Arithmetic},
    {"random.index", Plonky3},
    {"random.draw", Arithmetic},
    {"transcript.observe", Arkworks | Dalek | Plonky3 | Spongefish,
     Compatibility::Transcript},
    {"transcript.challenge", Arkworks | Dalek | Plonky3 | Spongefish,
     Compatibility::Transcript},
    {"transcript.index", Plonky3, Compatibility::Transcript},
    {"transcript.native.indexed.challenge",
     Arkworks | Dalek | Plonky3 | Spongefish, Compatibility::Transcript},
    {"transcript.native.indexed.observe.data",
     Arkworks | Dalek | Plonky3 | Spongefish, Compatibility::Transcript},
    // Only explicitly installed sampling suites grant IndexTranscript.
    {"transcript.native.indexed.index", Plonky3, Compatibility::Transcript},
    {"field_array.from_vector", Arkworks, Compatibility::Nominal,
     "bls12-381.fr"},
    {"field_array.at", Arkworks, Compatibility::Nominal, "bls12-381.fr"},
    {"field_array.get", Arkworks, Compatibility::Nominal, "bls12-381.fr"},
    {"fixed_vector.from_vector", Plonky3, Compatibility::Nominal, "koala-bear"},
    {"fixed_vector.to_vector", Plonky3, Compatibility::Nominal, "koala-bear"},
    {"fixed_vector.dot", Plonky3, Compatibility::Nominal, "koala-bear"}};

const generic::Operation *declaration(StringRef contract) {
  for (const auto &operation : executableOperationContracts())
    if (operation.name == contract)
      return &operation;
  return nullptr;
}

bool knownProvider(StringRef provider) {
  return provider == "native" || any_of(providerDomains, [&](const auto &row) {
           return row.provider == provider;
         });
}
} // namespace

bool implementationProviderSupports(StringRef provider, StringRef domain) {
  if (provider == "plonky3" && plonky3Field(domain))
    return true;
  return any_of(providerDomains, [&](const auto &row) {
    return row.provider == provider && row.domain == domain;
  });
}

ImplementationCatalog::ImplementationCatalog(
    std::vector<ImplementationDescriptor> descriptors,
    std::vector<ImplementationPreference> preferences)
    : descriptors(std::move(descriptors)), preferences(std::move(preferences)) {
}

Expected<ImplementationCatalog> ImplementationCatalog::create(
    std::vector<ImplementationDescriptor> descriptors,
    std::vector<ImplementationPreference> preferences) {
  ImplementationCatalog catalog(std::move(descriptors), std::move(preferences));
  std::set<std::pair<std::string, std::string>> keys;
  for (const auto &entry : catalog.descriptors) {
    const auto *logical = declaration(entry.contract);
    if (!logical || resourceUnitContract(entry.contract))
      return error("implementation-catalog-contract");
    if (entry.identity.empty() || !knownProvider(entry.provider) ||
        !keys.emplace(entry.contract, entry.identity).second)
      return error("implementation-catalog-entry");
    if (auto e = checkImplementationScope(entry, logical->signature.scope))
      return e;
    if (entry.family != ImplementationDescriptor::Family::Exact) {
      StringRef prefix =
          entry.family == ImplementationDescriptor::Family::Sequence
              ? "sequence."
          : entry.family == ImplementationDescriptor::Family::FieldArray
              ? "field_array."
              : "fixed_vector.";
      bool applicable =
          entry.family == ImplementationDescriptor::Family::Observation
              ? entry.contract == "transcript.native.indexed.observe.data"
              : StringRef(entry.contract).starts_with(prefix);
      if (!applicable || !entry.representations.empty())
        return error("implementation-catalog-entry");
    }
    std::set<
        std::tuple<std::string, std::string, std::optional<unsigned>, bool>>
        overrides;
    for (const auto &rep : entry.representations) {
      if (!installedDomains().representation(rep.kind, rep.domain,
                                             rep.identity))
        return error("implementation-catalog-representation");
      if (!implementationProviderSupports(entry.provider, rep.domain) ||
          !overrides.emplace(rep.kind, rep.domain, rep.port, rep.output).second)
        return error("implementation-catalog-representation");
      if (rep.port) {
        const auto &ports =
            rep.output ? logical->signature.outputs : logical->signature.inputs;
        if (*rep.port >= ports.size() ||
            ports[*rep.port].constructor != rep.kind)
          return error("implementation-catalog-representation");
      }
    }
  }
  keys.clear();
  for (const auto &preference : catalog.preferences) {
    const auto *entry =
        catalog.find(preference.contract, preference.implementation);
    if (!entry || entry->provider != preference.provider ||
        !keys.emplace(preference.contract, preference.provider).second)
      return error("implementation-catalog-default");
  }
  return catalog;
}

const ImplementationDescriptor *
ImplementationCatalog::find(StringRef contract,
                            StringRef implementation) const {
  for (const auto &entry : descriptors)
    if (entry.contract == contract && entry.identity == implementation)
      return &entry;
  return nullptr;
}

const ImplementationDescriptor *
ImplementationCatalog::preferred(StringRef contract, StringRef provider) const {
  for (const auto &entry : preferences)
    if (entry.contract == contract && entry.provider == provider)
      return find(contract, entry.implementation);
  return nullptr;
}

Expected<const ImplementationDescriptor *>
ImplementationCatalog::defaultFor(const BindingApplication &binding) const {
  const auto *logical = declaration(binding.contract);
  if (!logical)
    return error("binding-implementation");
  ArrayRef<std::string> arguments = binding.arguments;
  if (numericalContract(binding.contract)) {
    if (auto e = checkNumericalArguments(binding))
      return e;
    arguments = arguments.take_front(1);
  }
  auto identities = resolveStaticArguments(logical->signature.scope, arguments);
  if (!identities)
    return identities.takeError();
  const ImplementationDescriptor *selected = nullptr;
  for (const auto &preference : preferences) {
    if (preference.contract != binding.contract)
      continue;
    const auto *entry = find(preference.contract, preference.implementation);
    if (entry->compatibility != Compatibility::Independent &&
        installedDomains().defaultProvider(
            (*identities)[entry->providerTerm]) != entry->provider)
      continue;
    if (selected)
      return error("binding-implementation");
    selected = entry;
  }
  if (!selected)
    return error("binding-implementation");
  return selected;
}

Error checkImplementationScope(const ImplementationDescriptor &entry,
                               const generic::Scope &scope) {
  if (scope.terms.size() != scope.sorts.size())
    return error("implementation-catalog-policy");
  if (entry.compatibility == Compatibility::Independent) {
    if (entry.providerTerm != 0 || !entry.domains.empty() ||
        !all_of(scope.sorts,
                [](StringRef sort) { return sort == "Type" || sort == "Nat"; }))
      return error("implementation-catalog-policy");
    return Error::success();
  }
  if (entry.providerTerm >= scope.terms.size())
    return error("implementation-catalog-policy");
  StringRef sort = scope.sorts[entry.providerTerm];
  if (entry.compatibility == Compatibility::Transcript) {
    if (sort != "Transcript")
      return error("implementation-catalog-policy");
  } else if (entry.compatibility != Compatibility::Nominal || sort == "Codec" ||
             sort == "Transcript" || !is_contained(domainSorts(), sort)) {
    return error("implementation-catalog-policy");
  }
  // Follow only declared Domain projections to a nominal root. Applications
  // and Type/Nat terms cannot select a provider. Constant roots are resolved by
  // the same scope resolver as formal arguments, not by an argument offset.
  for (unsigned index = entry.providerTerm;;) {
    const auto &term = scope.terms[index];
    auto fixed = scope.constants.find(index);
    if (term.arguments || !is_contained(domainSorts(), scope.sorts[index]))
      return error("implementation-catalog-policy");
    if (!term.parent) {
      if (fixed != scope.constants.end() &&
          installedDomains().identitySort(fixed->second) != scope.sorts[index])
        return error("implementation-catalog-policy");
      break;
    }
    if (fixed != scope.constants.end() || *term.parent >= index ||
        associatedMemberSort(scope.sorts[*term.parent], term.name) !=
            scope.sorts[index])
      return error("implementation-catalog-policy");
    index = *term.parent;
  }
  for (const auto &domain : entry.domains)
    if (installedDomains().identitySort(domain) != sort ||
        !implementationProviderSupports(entry.provider, domain))
      return error("implementation-catalog-policy");
  return Error::success();
}

Error checkImplementationArguments(const ImplementationDescriptor &entry,
                                   const generic::Scope &scope,
                                   ArrayRef<std::string> identities) {
  if (auto e = checkImplementationScope(entry, scope)) {
    consumeError(std::move(e));
    return error("binding-implementation");
  }
  if (scope.sorts.size() != identities.size())
    return error("binding-implementation");
  if (entry.compatibility == Compatibility::Independent)
    return Error::success();
  if (!entry.domains.empty() &&
      !is_contained(entry.domains, identities[entry.providerTerm]))
    return error("binding-implementation");
  if (entry.compatibility == Compatibility::Transcript) {
    const auto &suite = identities[entry.providerTerm];
    if (!implementationProviderSupports(entry.provider, suite))
      return error("binding-implementation");
    StringRef field = associatedIdentity(suite, "ChallengeField");
    if (field.empty())
      return error("binding-implementation");
    for (auto [i, identity] : enumerate(identities)) {
      StringRef sort = scope.sorts[i];
      if (sort == "Type" || sort == "Nat" || sort == "Codec" ||
          identity == suite)
        continue;
      StringRef payloadField = identity;
      if (sort == "Group")
        payloadField = associatedIdentity(identity, "Scalar");
      else if (sort == "Commitment")
        payloadField = associatedIdentity(identity, "ValueField");
      // An extension-field suite also observes payloads over its base field.
      StringRef base = associatedIdentity(field, "BaseField");
      if (payloadField != field && (base.empty() || payloadField != base))
        return error("binding-implementation");
    }
    return Error::success();
  }
  if (entry.compatibility != Compatibility::Nominal)
    return error("binding-implementation");
  for (auto [i, identity] : enumerate(identities)) {
    StringRef sort = scope.sorts[i];
    if (sort == "Type" || sort == "Nat" || sort == "Codec")
      continue;
    if (!implementationProviderSupports(entry.provider, identity))
      return error("binding-implementation");
  }
  return Error::success();
}

Error applyImplementationRepresentations(const ImplementationDescriptor &entry,
                                         BoundOperation &operation) {
  for (const auto &rep : entry.representations) {
    if (!installedDomains().representation(rep.kind, rep.domain, rep.identity))
      return error("binding-representation");
    auto replace = [&](BoundType &port) -> Error {
      if (port.kind != rep.kind || port.identity != rep.domain ||
          !port.arguments.empty())
        return error("binding-representation");
      port.representation = rep.identity;
      return Error::success();
    };
    if (rep.port) {
      auto &ports = rep.output ? operation.outputs : operation.inputs;
      if (*rep.port >= ports.size())
        return error("binding-representation");
      if (auto e = replace(ports[*rep.port]))
        return e;
    } else {
      for (auto *ports : {&operation.inputs, &operation.outputs})
        for (auto &port : *ports)
          if (port.kind == rep.kind && port.identity == rep.domain)
            if (auto e = replace(port))
              return e;
    }
  }
  return Error::success();
}

Expected<std::vector<std::string>>
defaultPhysicalArguments(const BindingApplication &binding) {
  auto descriptor =
      installedImplementations().find(binding.contract, binding.implementation);
  if (!descriptor ||
      descriptor->family == ImplementationDescriptor::Family::Exact)
    return std::vector<std::string>{};
  auto logical = resolveLogicalBinding(binding);
  if (!logical)
    return logical.takeError();
  if (descriptor->family == ImplementationDescriptor::Family::Observation) {
    auto payload =
        operationContracts(binding.contract)->observation->payloadInput;
    auto selected = defaultRepresentation(logical->inputs[payload]);
    if (!selected)
      return selected.takeError();
    return std::vector<std::string>{selected->spelling()};
  }
  StringRef kind =
      descriptor->family == ImplementationDescriptor::Family::Sequence
          ? "sequence"
      : descriptor->family == ImplementationDescriptor::Family::FieldArray
          ? "field_array"
          : "fixed_vector";
  const BoundType *container = nullptr;
  for (const auto *ports : {&logical->inputs, &logical->outputs})
    for (const auto &port : *ports)
      if (!container && port.kind == kind)
        container = &port;
  if (!container)
    return error("binding-representation");
  if (descriptor->provider == "blst")
    return std::vector<std::string>{
        container->spelling() + "@blst/" +
        (kind == "field_array" ? "field-array" : "fixed-vector") + "[blst/fr]"};
  auto physical = defaultRepresentation(*container);
  if (!physical)
    return physical.takeError();
  return std::vector<std::string>{physical->spelling()};
}

Error applyImplementationFamily(const ImplementationDescriptor &entry,
                                const BindingApplication &binding,
                                BoundOperation &operation) {
  using Family = ImplementationDescriptor::Family;
  if (entry.family == Family::Observation) {
    if (binding.physicalArguments.size() > 1)
      return error("binding-representation");
    auto payload =
        operationContracts(binding.contract)->observation->payloadInput;
    auto selected =
        binding.physicalArguments.empty()
            ? defaultRepresentation(operation.inputs[payload])
            : parseBoundType(binding.physicalArguments.front(), true);
    if (!selected)
      return selected.takeError();
    if (!(erasePhysicalType(*selected) == operation.inputs[payload]))
      return error("binding-representation");
    if (!nativeMessageData(*selected))
      return error("native-proof-wire-type");
    for (auto *ports : {&operation.inputs, &operation.outputs})
      for (auto [index, port] : enumerate(*ports)) {
        if (ports == &operation.inputs && index == payload) {
          port = *selected;
          continue;
        }
        auto physical = defaultRepresentation(port);
        if (!physical)
          return physical.takeError();
        port = std::move(*physical);
      }
    return Error::success();
  }
  if (entry.family == Family::Exact) {
    if (!binding.physicalArguments.empty())
      return error("binding-representation");
    for (auto *ports : {&operation.inputs, &operation.outputs})
      for (auto &port : *ports) {
        auto physical = defaultRepresentation(port);
        if (!physical)
          return physical.takeError();
        port = std::move(*physical);
      }
    return applyImplementationRepresentations(entry, operation);
  }
  Expected<std::vector<std::string>> parameters = binding.physicalArguments;
  if (binding.physicalArguments.empty()) {
    // Empty parameters mean the one installed default layout, independently
    // of the selected implementation's storage. No provider fallback.
    StringRef kind = entry.family == Family::Sequence     ? "sequence"
                     : entry.family == Family::FieldArray ? "field_array"
                                                          : "fixed_vector";
    const BoundType *container = nullptr;
    for (const auto *ports : {&operation.inputs, &operation.outputs})
      for (const auto &port : *ports)
        if (!container && port.kind == kind)
          container = &port;
    if (!container)
      return error("binding-representation");
    auto selected = defaultRepresentation(*container);
    if (!selected)
      return selected.takeError();
    parameters = std::vector<std::string>{selected->spelling()};
  }
  if (!parameters)
    return parameters.takeError();
  if (parameters->size() != 1)
    return error("binding-representation");
  auto selected = parseBoundType(parameters->front(), true);
  if (!selected)
    return selected.takeError();
  StringRef kind = entry.family == Family::Sequence     ? "sequence"
                   : entry.family == Family::FieldArray ? "field_array"
                                                        : "fixed_vector";
  if (selected->kind != kind || !selected->physicalChildren ||
      selected->physicalChildren->size() != 1)
    return error("binding-representation");
  auto logical = erasePhysicalType(*selected);
  // The first container port is the family's schema. A sequence element may
  // itself be a sequence, with a different logical schema and child layout.
  const BoundType *container = nullptr;
  for (const auto *ports : {&operation.inputs, &operation.outputs})
    for (const auto &port : *ports)
      if (!container && port.kind == kind)
        container = &port;
  if (!container || !(*container == logical))
    return error("binding-representation");
  const auto &element = selected->physicalChildren->front();
  if (entry.family != Family::Sequence) {
    StringRef expected =
        entry.provider == "blst"
            ? (kind == "field_array" ? "blst/field-array" : "blst/fixed-vector")
        : entry.provider == "arkworks" ? "arkworks.field-array/0"
                                       : "plonky3.fixed-vector/0";
    if (selected->representation != expected)
      return error("binding-representation");
  }
  auto select = [&](BoundType &port, bool output, unsigned index) -> Error {
    if (port == logical) {
      port = *selected;
      return Error::success();
    }
    bool elementPort =
        entry.family == Family::Sequence
            ? ((binding.contract == "sequence.append" && !output &&
                index == 1) ||
               (binding.contract == "sequence.at" && output && index == 0))
            : port.kind == "field";
    if (elementPort) {
      if (!(port == erasePhysicalType(element)))
        return error("binding-representation");
      port = element;
      return Error::success();
    }
    if (entry.family != Family::Sequence && port.kind == "vector") {
      auto physical = parseBoundType(port.spelling() + "@" +
                                         (entry.provider == "blst" ? "blst/fr"
                                          : entry.provider == "arkworks"
                                              ? "arkworks.fr-vector/0"
                                              : "plonky3.koala-bear-vector/0"),
                                     true);
      if (!physical)
        return physical.takeError();
      port = std::move(*physical);
      return Error::success();
    }
    auto physical = defaultRepresentation(port);
    if (!physical)
      return physical.takeError();
    port = std::move(*physical);
    return Error::success();
  };
  for (auto [i, port] : enumerate(operation.inputs))
    if (auto e = select(port, false, i))
      return e;
  for (auto [i, port] : enumerate(operation.outputs))
    if (auto e = select(port, true, i))
      return e;
  return Error::success();
}

const ImplementationCatalog &installedImplementations() {
  static const ImplementationCatalog catalog = [] {
    for (const auto &row : providerDomains)
      if (!installedDomains().domain(row.domain))
        report_fatal_error("invalid installed implementation provider domain",
                           false);
    std::vector<ImplementationDescriptor> entries;
    std::vector<ImplementationPreference> preferences;
    const std::pair<unsigned, StringRef> providers[] = {
        {Arkworks, "arkworks"},
        {Dalek, "dalek"},
        {Plonky3, "plonky3"},
        {Spongefish, "spongefish"},
        {Native, "native"}};
    // Rows naming one contract, provider and policy with different domain
    // restrictions describe a single implementation admitting each domain.
    auto install = [&](const ContractRow &row, StringRef domain) {
      for (const auto &[flag, provider] : providers)
        if (row.providers & flag) {
          std::string identity = (provider + "/" + row.contract).str();
          auto existing = find_if(entries, [&](const auto &entry) {
            return entry.contract == row.contract && entry.identity == identity;
          });
          if (existing != entries.end()) {
            if (existing->compatibility != row.compatibility ||
                existing->domains.empty() || domain.empty() ||
                is_contained(existing->domains, domain))
              report_fatal_error("ambiguous installed implementation row",
                                 false);
            existing->domains.push_back(domain.str());
            continue;
          }
          std::vector<std::string> domains;
          if (!domain.empty())
            domains.push_back(domain.str());
          entries.push_back({row.contract.str(), identity, provider.str(),
                             row.compatibility, std::move(domains)});
          preferences.push_back({row.contract.str(), provider.str(), identity});
        }
    };
    for (const auto &row : contractRows) {
      if (row.fields == FieldSet::None) {
        install(row, row.domain);
        continue;
      }
      if (!row.domain.empty() || row.providers != Plonky3)
        report_fatal_error("ambiguous installed implementation row", false);
      for (const auto &field : plonky3Fields())
        if (row.fields != FieldSet::Montgomery32 || field.montgomery32)
          install(row, field.identity);
      if (row.fields == FieldSet::LittleEndian)
        for (StringRef field : {"gf2-64.pentanomial-4-3-1",
                                "gf2-64.pentanomial-4-3-1.ext3-trinomial1"})
          install(row, field);
    }
    // Explicit BN254 provider menu. These positive operation and physical-port
    // inventories do not add a canonical default or a protocol-specific route.
    for (StringRef contract : {"field.constant",    "field.from_index",
                               "field.add",         "field.sub",
                               "field.neg",         "field.mul",
                               "field.inverse",     "field.equal",
                               "vector.empty",      "vector.constant",
                               "vector.splat",      "vector.append",
                               "vector.at",         "vector.get",
                               "vector.length",     "vector.length_check",
                               "vector.add",        "vector.sub",
                               "vector.mul",        "vector.dot",
                               "vector.scale",      "vector.sum",
                               "vector.product",    "vector.split",
                               "vector.concat",     "vector.slice",
                               "vector.equal",      "curve.generator",
                               "curve.identity",    "curve.add",
                               "curve.neg",         "curve.equal",
                               "curve.nonidentity", "curve.scale",
                               "curve.empty",       "curve.append",
                               "curve.at",          "curve.get",
                               "curve.length",      "curve.vector_add",
                               "curve.scale_each",  "curve.vector_scale",
                               "curve.split",       "curve.concat",
                               "curve.msm",         "pairing.check"}) {
      std::string implementation =
          ("halo2curves-axiom/resident/" + contract).str();
      entries.push_back(
          {contract.str(),
           implementation,
           "halo2curves-axiom",
           Compatibility::Nominal,
           contract.starts_with("curve.")
               ? std::vector<std::string>{"bn254.g1", "bn254.g2"}
               : std::vector<std::string>{"bn254.fr"},
           {{"field", "bn254.fr", "halo2curves-axiom/bn254.fr"},
            {"vector", "bn254.fr", "halo2curves-axiom/bn254.fr"},
            {"group", "bn254.g1", "halo2curves-axiom/bn254.g1"},
            {"groups", "bn254.g1", "halo2curves-axiom/bn254.g1"},
            {"group", "bn254.g2", "halo2curves-axiom/bn254.g2"},
            {"groups", "bn254.g2", "halo2curves-axiom/bn254.g2"}}});
      entries.back().requiresExplicitSelection = true;
      preferences.push_back(
          {contract.str(), "halo2curves-axiom", implementation});
    }
    // Algorithm and layout alternatives do not add a default preference.
    // Resident alternatives have exact ports and deliberately no preference.
    for (StringRef contract : {"field.constant",
                               "field.from_index",
                               "field.add",
                               "field.sub",
                               "field.neg",
                               "field.mul",
                               "field.inverse",
                               "field.equal",
                               "vector.empty",
                               "vector.append",
                               "vector.at",
                               "vector.get",
                               "vector.length",
                               "vector.length_check",
                               "vector.add",
                               "vector.sub",
                               "vector.mul",
                               "vector.dot",
                               "vector.scale",
                               "vector.sum",
                               "vector.product",
                               "vector.split",
                               "vector.concat",
                               "vector.slice",
                               "vector.equal",
                               "vector.splat",
                               "vector.powers",
                               "vector.bit_reverse",
                               "vector.bit_reverse_rows",
                               "vector.constant",
                               "vector.fill",
                               "vector.find_last",
                               "vector.gather",
                               "vector.geometric",
                               "vector.interleave",
                               "vector.inverse",
                               "vector.kronecker",
                               "vector.matvec",
                               "vector.prefix_product",
                               "vector.prefix_sum",
                               "vector.rotate",
                               "vector.scatter_sum",
                               "vector.transpose"})
      entries.push_back({contract.str(),
                         ("blst/resident/" + contract).str(),
                         "blst",
                         Compatibility::Nominal,
                         {"bls12-381.fr"},
                         {{"field", "bls12-381.fr", "blst/fr"},
                          {"vector", "bls12-381.fr", "blst/fr"}}});
    for (StringRef contract :
         {"curve.generator", "curve.identity", "curve.add", "curve.neg",
          "curve.equal", "curve.nonidentity", "curve.scale", "curve.empty",
          "curve.append", "curve.at", "curve.get", "curve.length",
          "curve.vector_add", "curve.scale_each", "curve.vector_scale",
          "curve.split", "curve.concat", "curve.msm", "pairing.check"})
      entries.push_back(
          {contract.str(),
           ("blst/resident/" + contract).str(),
           "blst",
           Compatibility::Nominal,
           contract == "pairing.check"
               ? std::vector<std::string>{"bls12-381.fr"}
               : std::vector<std::string>{"bls12-381.g1", "bls12-381.g2"},
           {{"field", "bls12-381.fr", "blst/fr"},
            {"vector", "bls12-381.fr", "blst/fr"},
            {"group", "bls12-381.g1", "blst/g1"},
            {"groups", "bls12-381.g1", "blst/g1"},
            {"group", "bls12-381.g2", "blst/g2"},
            {"groups", "bls12-381.g2", "blst/g2"}}});
    entries.push_back({"vector.dot",
                       "arkworks-pairwise/vector.dot",
                       "arkworks",
                       Compatibility::Nominal,
                       {"bls12-381.fr"}});
    for (StringRef contract :
         {"poly.product_sum", "poly.product_round", "poly.boundary",
          "poly.round_evaluate", "poly.fold", "poly.evaluate",
          "poly.empty_point", "poly.append_point", "vector.from_table",
          "vector.to_table"})
      entries.push_back({contract.str(),
                         ("arkworks-msb/" + contract).str(),
                         "arkworks",
                         Compatibility::Nominal,
                         {"bls12-381.fr"},
                         {{"table", "bls12-381.fr", "arkworks.mle-msb/0"}}});
    entries.push_back(
        {"vector.mul",
         "arkworks-diagonal/vector.mul",
         "arkworks",
         Compatibility::Nominal,
         {"bls12-381.fr"},
         {{"vector", "bls12-381.fr", "arkworks.fr-diagonal/0", 0, true}}});
    entries.push_back(
        {"vector.dot",
         "arkworks-diagonal/vector.dot",
         "arkworks",
         Compatibility::Nominal,
         {"bls12-381.fr"},
         {{"vector", "bls12-381.fr", "arkworks.fr-diagonal/0", 1}}});
    entries.push_back({"curve.scale_each",
                       "dalek-diagonal/curve.scale_each",
                       "dalek",
                       Compatibility::Nominal,
                       {"ristretto255.group"},
                       {{"groups", "ristretto255.group",
                         "dalek.ristretto-diagonal/0", 0, true}}});
    entries.push_back(
        {"curve.msm",
         "dalek-diagonal/curve.msm",
         "dalek",
         Compatibility::Nominal,
         {"ristretto255.group"},
         {{"groups", "ristretto255.group", "dalek.ristretto-diagonal/0", 1}}});
    for (StringRef contract : {"field_array.from_vector", "field_array.at",
                               "field_array.get", "fixed_vector.from_vector",
                               "fixed_vector.to_vector", "fixed_vector.dot"})
      entries.push_back({contract.str(),
                         ("blst/resident/" + contract).str(),
                         "blst",
                         Compatibility::Nominal,
                         {"bls12-381.fr"}});
    for (auto &entry : entries) {
      if (entry.contract == "curve.msm" && entry.provider == "blst")
        entry.requiresExplicitSelection = true;
      if (entry.contract == "transcript.native.indexed.observe.data")
        entry.family = ImplementationDescriptor::Family::Observation;
      if (StringRef(entry.contract).starts_with("sequence."))
        entry.family = ImplementationDescriptor::Family::Sequence;
      if (StringRef(entry.contract).starts_with("field_array."))
        entry.family = ImplementationDescriptor::Family::FieldArray;
      if (StringRef(entry.contract).starts_with("fixed_vector."))
        entry.family = ImplementationDescriptor::Family::FixedVector;
    }
    auto result = ImplementationCatalog::create(std::move(entries),
                                                std::move(preferences));
    if (!result)
      report_fatal_error(Twine("invalid installed implementation catalog: ") +
                             toString(result.takeError()),
                         false);
    return std::move(*result);
  }();
  return catalog;
}
} // namespace zkc::protocol
