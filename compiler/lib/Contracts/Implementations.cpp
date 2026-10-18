#include "zkc/Contracts/Implementations.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/ResourceUnit.h"
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
    {"plonky3", "koala-bear"},
    {"plonky3", "koala-bear.ext8-binomial3"},
    {"plonky3", "koala-bear.ext4-binomial3"},
    {"plonky3", "merlin3.koala-bear.ext8-binomial3.rejection31le/0"},
    {"plonky3",
     "hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0"},
    {"plonky3", "rows.merkle-keccak256.koala-bear/0"},
    {"plonky3", "rows.merkle-keccak256.koala-bear.ext8-binomial3/0"},
    {"plonky3", "rows.merkle-poseidon2-16.koala-bear/0"},
    {"plonky3", "rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0"},
    {"plonky3", "gf2-64.pentanomial-4-3-1"},
    {"plonky3", "gf2-64.pentanomial-4-3-1.ext3-trinomial1"},
    {"spongefish", "spongefish0.8.0.keccak.bls12-381.fr64be/0"}};

// One provider can serve fields with different presentations. Rows whose
// kernels read integer residue coordinates name the KoalaBear family, so the
// binary fields under the same provider do not inherit them
// (docs/spec/realization/external-constructions.md).
constexpr StringRef koalaFamily[] = {"koala-bear", "koala-bear.ext8-binomial3",
                                     "koala-bear.ext4-binomial3"};
constexpr StringRef littleEndianFields[] = {
    "koala-bear", "koala-bear.ext8-binomial3", "koala-bear.ext4-binomial3",
    "gf2-64.pentanomial-4-3-1", "gf2-64.pentanomial-4-3-1.ext3-trinomial1"};

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
  // Several domain restrictions of one row, as if listed one per row.
  ArrayRef<StringRef> domains = {};
};
constexpr auto Nominal = Compatibility::Nominal;
constexpr ContractRow contractRows[] = {
    {"ring.point", Plonky3, Nominal, {}, koalaFamily},
    {"ring.rows", Plonky3, Nominal, {}, koalaFamily},
    {"ring.coefficients", Plonky3, Nominal, {}, koalaFamily},
    {"ring.affine_sum", Plonky3, Nominal, {}, koalaFamily},
    {"relation.table_rows", Plonky3, Nominal, {}, koalaFamily},
    {"relation.table_shape", Plonky3, Nominal, {}, koalaFamily},
    {"relation.table_input", Plonky3, Nominal, {}, koalaFamily},
    {"relation.table_scope", Plonky3, Nominal, {}, koalaFamily},
    {"relation.table_point", Plonky3, Nominal, {}, koalaFamily},
    {"relation.table_points", Plonky3, Nominal, {}, koalaFamily},
    {"relation.table_widths", Plonky3, Nominal, {}, koalaFamily},
    {"relation.table_policy", Plonky3, Nominal, {}, koalaFamily},
    {"relation.table_interactions", Plonky3, Nominal, {}, koalaFamily},
    {"relation.table_interaction", Plonky3, Nominal, {}, koalaFamily},
    {"relation.table_record_points", Plonky3, Nominal, {}, koalaFamily},
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
    // KoalaBear and its installed extensions: four-byte words per coordinate.
    // Binary fields: little-endian bit patterns, with no Montgomery form.
    {"encoding.field_le", Plonky3, Nominal, {}, littleEndianFields},
    {"encoding.field_from_le", Plonky3, Nominal, {}, littleEndianFields},
    {"encoding.fields_le", Plonky3, Nominal, {}, littleEndianFields},
    {"encoding.fields_from_le", Plonky3, Nominal, {}, littleEndianFields},
    {"encoding.field_montgomery_le", Plonky3, Nominal, {}, koalaFamily},
    {"encoding.field_from_montgomery_le", Plonky3, Nominal, {}, koalaFamily},
    {"encoding.fields_montgomery_le", Plonky3, Nominal, {}, koalaFamily},
    {"encoding.fields_from_montgomery_le", Plonky3, Nominal, {}, koalaFamily},
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
    {"poly.coset_interpolate", Arkworks | Plonky3},
    {"poly.domain_point", Arkworks | Plonky3},
    {"poly.domain_root", Arkworks | Plonky3},
    {"poly.domain_points", Arkworks | Plonky3},
    {"poly.even_odd_fold", Arkworks | Plonky3},
    {"poly.opening_quotient", Arkworks | Plonky3},
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
    // Only the octic suites grant IndexTranscript.
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
    std::set<std::tuple<std::string, std::optional<unsigned>, bool>> overrides;
    for (const auto &rep : entry.representations) {
      if (!installedDomains().representation(rep.kind, rep.domain,
                                             rep.identity))
        return error("implementation-catalog-representation");
      if (!implementationProviderSupports(entry.provider, rep.domain) ||
          !overrides.emplace(rep.kind, rep.port, rep.output).second)
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
  auto identities =
      resolveStaticArguments(logical->signature.scope, binding.arguments);
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
          if (port.kind == rep.kind)
            if (auto e = replace(port))
              return e;
    }
  }
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
      if (!row.domain.empty() && !row.domains.empty())
        report_fatal_error("ambiguous installed implementation row", false);
      if (row.domains.empty())
        install(row, row.domain);
      for (StringRef domain : row.domains)
        install(row, domain);
    }
    // Algorithm and layout alternatives do not add a default preference.
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
