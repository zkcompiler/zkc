#ifndef ZKC_PROTOCOL_DOMAINS_H
#define ZKC_PROTOCOL_DOMAINS_H

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include <string>
#include <vector>

namespace zkc::protocol {

struct AssociatedIdentity {
  std::string member, identity;
};

/// Closed nominal facts, checked against the binding layer's static vocabulary.
/// Codec identities have their own payload records below.
struct NominalDomain {
  std::string identity, sort;
  std::vector<AssociatedIdentity> associated;
  std::vector<std::string> capabilities;
  /// Optional characteristic for installed natural casts: closed literals are
  /// canonical embedded prime-subfield representatives below this bound.
  /// This is neither field cardinality nor a primality proof.
  std::string modulus = {};
};

struct CodecIdentity {
  std::string identity, kind, domain;
};

/// Applicability is the complete (kind, domain, identity) tuple. A
/// representation identity may be shared by several tuples. An optional layout
/// names an explicit selection, such as "msb"; it does not select an
/// optimization policy.
struct DomainRepresentation {
  std::string identity, kind, domain;
  bool isDefault = false;
  std::string layout;
};

/// Immutable, owned installation data. Construction validates the whole closed
/// catalog before exposing any lookups. Missing lookups return
/// null/empty/false. Returned pointers and StringRefs live as long as this
/// catalog, unless moved. There is no mutation, external registration, or
/// operation registry here. Logical kernel signatures and backend realizations
/// are independent obligations: an applicable representation or nominal fact
/// does not establish either one.
class DomainCatalog {
public:
  static llvm::Expected<DomainCatalog>
  create(std::vector<NominalDomain> domains, std::vector<CodecIdentity> codecs,
         std::vector<DomainRepresentation> representations);

  DomainCatalog(const DomainCatalog &) = default;
  DomainCatalog(DomainCatalog &&) = default;
  DomainCatalog &operator=(const DomainCatalog &) = delete;
  DomainCatalog &operator=(DomainCatalog &&) = delete;

  const NominalDomain *domain(llvm::StringRef identity) const;
  const CodecIdentity *codec(llvm::StringRef identity) const;
  llvm::ArrayRef<NominalDomain> allDomains() const { return domains; }
  llvm::ArrayRef<CodecIdentity> allCodecs() const { return codecs; }
  llvm::StringRef identitySort(llvm::StringRef identity) const;
  llvm::StringRef associatedIdentity(llvm::StringRef identity,
                                     llvm::StringRef member) const;
  bool hasFact(llvm::StringRef predicate,
               llvm::ArrayRef<std::string> arguments) const;

  /// Multiple codecs for one payload remain explicitly usable, but offer no
  /// implicit default. The bool payload has an empty domain; no other kind
  /// does.
  const CodecIdentity *defaultCodec(llvm::StringRef kind,
                                    llvm::StringRef domain) const;
  const DomainRepresentation *representation(llvm::StringRef kind,
                                             llvm::StringRef domain,
                                             llvm::StringRef identity) const;
  const DomainRepresentation *
  defaultRepresentation(llvm::StringRef kind, llvm::StringRef domain) const;
  const DomainRepresentation *
  representationForLayout(llvm::StringRef kind, llvm::StringRef domain,
                          llvm::StringRef layout) const;

private:
  DomainCatalog(std::vector<NominalDomain> domains,
                std::vector<CodecIdentity> codecs,
                std::vector<DomainRepresentation> representations);
  std::vector<NominalDomain> domains;
  std::vector<CodecIdentity> codecs;
  std::vector<DomainRepresentation> representations;
};

/// The current BLS/PCS and Ristretto/Merlin installation. Invalid built-in data
/// is a fatal installation error, never a partially usable catalog. Lifetime is
/// static.
const DomainCatalog &installedDomains();

} // namespace zkc::protocol

#endif
