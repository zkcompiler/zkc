#ifndef ZKC_CONTRACTS_IMPLEMENTATIONS_H
#define ZKC_CONTRACTS_IMPLEMENTATIONS_H

#include "zkc/Contracts/Bindings.h"
#include <optional>

namespace zkc::protocol {

/// Exact replacement of a default physical port representation. No index means
/// all ports of this kind; otherwise only the named input or output is changed.
struct ImplementationRepresentation {
  std::string kind, domain, identity;
  std::optional<unsigned> port = {};
  bool output = false;
};

/// Installed selection data, not evidence of execution or semantic correctness.
/// Logical signatures, requirements and type formation remain declaration
/// owned.
struct ImplementationDescriptor {
  enum class Compatibility { Nominal, Transcript, Independent };
  std::string contract, identity, provider;
  Compatibility compatibility = Compatibility::Nominal;
  /// Optional exact identity of providerTerm, in addition to provider
  /// membership.
  std::string domain = {};
  std::vector<ImplementationRepresentation> representations = {};
  /// Index in the resolved logical scope, not in the supplied argument list.
  /// Selects a Domain root (including a constant) or associated Domain
  /// projection. Nominal excludes Codec/Transcript; Transcript requires a
  /// Transcript term. Independent has no selector and retains the value zero.
  unsigned providerTerm = 0;
};

/// Preference is independent of descriptor applicability. No entry means no
/// default, even when a descriptor is explicitly selectable.
struct ImplementationPreference {
  std::string contract, provider, implementation;
};

/// Immutable, build-time installation. Creation validates exact logical and
/// representation references. There is no runtime registration or plugin
/// loader.
class ImplementationCatalog {
public:
  static llvm::Expected<ImplementationCatalog>
      create(std::vector<ImplementationDescriptor>,
             std::vector<ImplementationPreference>);
  llvm::ArrayRef<ImplementationDescriptor> all() const { return descriptors; }
  const ImplementationDescriptor *find(llvm::StringRef contract,
                                       llvm::StringRef implementation) const;
  const ImplementationDescriptor *preferred(llvm::StringRef contract,
                                            llvm::StringRef provider) const;
  /// Resolves the declaration's scope before consulting provider preferences.
  /// A preference is a candidate; full applicability is checked separately.
  llvm::Expected<const ImplementationDescriptor *>
  defaultFor(const BindingApplication &) const;

private:
  ImplementationCatalog(std::vector<ImplementationDescriptor> descriptors,
                        std::vector<ImplementationPreference> preferences);
  std::vector<ImplementationDescriptor> descriptors;
  std::vector<ImplementationPreference> preferences;
};

const ImplementationCatalog &installedImplementations();
/// Nominal compatibility, independent of the domain's default preference.
bool implementationProviderSupports(llvm::StringRef provider,
                                    llvm::StringRef domain);
/// Validate compatibility policy and selector against an already formed
/// logical scope. Independent permits only Type/Nat terms (or an empty scope).
/// This is not a replacement for logical scope formation or static admission.
llvm::Error checkImplementationScope(const ImplementationDescriptor &,
                                     const generic::Scope &);
/// Call after logical static arguments and requirements have been checked.
llvm::Error
checkImplementationArguments(const ImplementationDescriptor &,
                             const generic::Scope &,
                             llvm::ArrayRef<std::string> identities);
/// Call after default physical ports have been formed. Exact tuple and port
/// checks remain mandatory even for installed descriptors.
llvm::Error applyImplementationRepresentations(const ImplementationDescriptor &,
                                               BoundOperation &);
} // namespace zkc::protocol

#endif
