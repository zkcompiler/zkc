#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Instances.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/ErrorHandling.h"
#include <set>
#include <tuple>
#include <utility>

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
  if (kind == "variant" || kind == "resource_unit")
    return false;
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
                             std::vector<LogicalTypeInstance> logicalTypes,
                             std::vector<CodecIdentity> codecs,
                             std::vector<DomainRepresentation> representations,
                             std::vector<DefaultProvider> defaultProviders)
    : domains(std::move(domains)), logicalTypes(std::move(logicalTypes)),
      codecs(std::move(codecs)), representations(std::move(representations)),
      defaultProviders(std::move(defaultProviders)) {}

Expected<DomainCatalog>
DomainCatalog::create(std::vector<NominalDomain> domains,
                      std::vector<LogicalTypeInstance> logicalTypes,
                      std::vector<CodecIdentity> codecs,
                      std::vector<DomainRepresentation> representations,
                      std::vector<DefaultProvider> defaultProviders) {
  DomainCatalog catalog(std::move(domains), std::move(logicalTypes),
                        std::move(codecs), std::move(representations),
                        std::move(defaultProviders));
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
    if (d.sort == "Codec" || !is_contained(domainSorts(), d.sort))
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
  std::set<std::pair<std::string, std::string>> admitted;
  for (const auto &type : catalog.logicalTypes) {
    if (!applicableType(catalog, type.kind, type.domain))
      return invalid("invalid logical type instance");
    if (!admitted.emplace(type.kind, type.domain).second)
      return invalid("duplicate logical type instance");
  }
  for (const auto &c : catalog.codecs) {
    if (!applicableType(catalog, c.kind, c.domain))
      return invalid("invalid codec payload domain");
    std::vector<std::string> sorts{"Codec"};
    if (!c.domain.empty())
      sorts.push_back(catalog.identitySort(c.domain).str());
    if (!validPredicate("Encodes." + c.kind, sorts))
      return invalid("invalid codec payload kind");
    if (!catalog.admitsLogicalType(c.kind, c.domain))
      return invalid("unadmitted codec payload type");
  }
  // A shared scalar field does not identify a pairing's ordered source groups.
  // Validate the complete association before exposing a PairingField fact;
  // pairing groups occur only on PairingField rows.
  for (const auto &d : catalog.domains) {
    if (!is_contained(d.capabilities, "PairingField")) {
      if (any_of(d.associated, [](const auto &a) {
            return a.member == "PairingG1" || a.member == "PairingG2" ||
                   a.member == "PairingGT";
          }))
        return invalid("invalid pairing group association");
      continue;
    }
    StringRef g1 = catalog.associatedIdentity(d.identity, "PairingG1");
    StringRef g2 = catalog.associatedIdentity(d.identity, "PairingG2");
    if (g1.empty() || g2.empty() || g1 == g2 ||
        !catalog.hasFact("ScalarAction", {g1.str()}) ||
        !catalog.hasFact("ScalarAction", {g2.str()}) ||
        catalog.associatedIdentity(g1, "Scalar") != d.identity ||
        catalog.associatedIdentity(g2, "Scalar") != d.identity)
      return invalid("invalid pairing group association");
    StringRef gt = catalog.associatedIdentity(d.identity, "PairingGT");
    // Predicate-only catalogs need not expose a target representation.
    if (!gt.empty() &&
        (gt == g1 || gt == g2 || !catalog.hasFact("ScalarAction", {gt.str()}) ||
         catalog.associatedIdentity(gt, "Scalar") != d.identity))
      return invalid("invalid pairing target association");
  }
  std::set<std::tuple<std::string, std::string, std::string>> legal, layouts;
  std::set<std::pair<std::string, std::string>> defaults;
  for (const auto &r : catalog.representations) {
    if (!validName(r.identity))
      return invalid("invalid representation identity");
    if (!applicableType(catalog, r.kind, r.domain))
      return invalid("invalid representation domain");
    if (!catalog.admitsLogicalType(r.kind, r.domain))
      return invalid("unadmitted representation type");
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
  std::set<std::string> providerDomains;
  for (const auto &selection : catalog.defaultProviders) {
    if (!catalog.domain(selection.domain))
      return invalid("invalid provider domain");
    if (!validName(selection.provider) ||
        StringRef(selection.provider).contains('/'))
      return invalid("invalid default provider");
    if (!providerDomains.insert(selection.domain).second)
      return invalid("duplicate default provider");
  }
  return catalog;
}

bool DomainCatalog::admitsLogicalType(StringRef kind,
                                      StringRef identity) const {
  return any_of(logicalTypes, [&](const auto &type) {
    return type.kind == kind && type.domain == identity;
  });
}

StringRef DomainCatalog::defaultProvider(StringRef identity) const {
  for (const auto &selection : defaultProviders)
    if (selection.domain == identity)
      return selection.provider;
  return {};
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

namespace {
namespace generated = instances;
namespace physical = installation;

[[noreturn]] void invalidInstallation(const Twine &reason) {
  report_fatal_error(Twine("invalid installed domain catalog: ") + reason,
                     false);
}
} // namespace

const DomainCatalog &installedDomains() {
  // Built from the generated installed-instance and installation tables in
  // declared order, through the validating constructor.
  static const DomainCatalog catalog = [] {
    std::vector<NominalDomain> domains;
    for (const auto &row : generated::domains()) {
      std::vector<AssociatedIdentity> associated;
      for (const auto &member : row.members)
        associated.push_back({member.member, member.identity});
      domains.push_back({row.identity, row.sort, std::move(associated),
                         row.capabilities,
                         row.field ? row.field->characteristic : ""});
    }
    std::vector<LogicalTypeInstance> logicalTypes;
    for (const auto &row : generated::logicalTypes())
      logicalTypes.push_back({row.kind, row.domain});
    std::vector<CodecIdentity> codecs;
    for (const auto &row : generated::codecs())
      codecs.push_back({row.identity, row.kind, row.domain});
    std::vector<DomainRepresentation> representations;
    for (const auto &row : physical::representations())
      representations.push_back(
          {row.identity, row.kind, row.domain, row.isDefault, row.layout});
    // Nominal provider policy does not follow representation spelling or
    // associated fields. Implementation legality is checked separately.
    std::vector<DefaultProvider> providers;
    for (const auto &row : physical::providers())
      providers.push_back({row.domain, row.defaultProvider});
    auto result = DomainCatalog::create(
        std::move(domains), std::move(logicalTypes), std::move(codecs),
        std::move(representations), std::move(providers));
    if (!result)
      invalidInstallation(toString(result.takeError()));
    return std::move(*result);
  }();
  return catalog;
}
} // namespace zkc::protocol
