#ifndef ZKC_MATHEMATICAL_INSTALLATION_H
#define ZKC_MATHEMATICAL_INSTALLATION_H

#include "zkc/Contracts/Services.h"
#include "zkc/Mathematical/Registry.h"

namespace zkc::mathematical {

struct WireRealization {
  std::string codec;
  protocol::BoundType payload;
  // The common message carrier selects its installed codec by payload type.
  bool implicitDefault;
};

/// A closed installation selected by the compiler host, not by the input's
/// manifest. Signatures and totality come from the existing logical contracts;
/// nominal types and wires come from the existing domain catalog. This adapter
/// covers closed unary nominal values and Fin 2, with no operation attributes.
/// Scalar entropy services reuse the common state-transition contracts. Law
/// packages require their own installed interpretations.
///
/// Descriptor digests pin this adapter's resolved declarations. They are not
/// code hashes or proofs of the native kernels, codecs or mathematical laws.
class Installation final : public Registry {
  struct Operation {
    raw::Identity identity;
    protocol::BindingApplication binding;
    protocol::BoundOperation signature;
  };
  struct Wire {
    raw::Identity identity;
    WireRealization realization;
  };
  struct Service {
    raw::Identity identity;
    protocol::EntropyService descriptor;
  };
  raw::Manifest packages;
  std::vector<Operation> operations;
  std::vector<Wire> wires;
  std::vector<Service> services;
  Installation() = default;

public:
  /// Rejects physical selections, ordered contracts, attribute schemas and
  /// signatures outside this adapter's explicit supported type subset.
  static llvm::Expected<Installation>
  create(llvm::ArrayRef<protocol::BindingApplication> operations,
         llvm::ArrayRef<std::string> codecs,
         llvm::ArrayRef<protocol::BindingApplication> services = {});

  const raw::Manifest &manifest() const { return packages; }
  /// Mapping used by later realization. The identity must match the installed
  /// descriptor in full; authored names alone cannot choose a binding.
  const protocol::BindingApplication *binding(const raw::Identity &) const;
  const protocol::EntropyService *serviceBinding(const raw::Identity &) const;
  const WireRealization *wireBinding(const raw::Identity &) const;
  llvm::Expected<protocol::BoundType> logicalType(TypeId, const TypeTable &,
                                                  const raw::Manifest &) const;

  llvm::Error identity(Category, const raw::Identity &,
                       const raw::Manifest &) const override;
  llvm::Error domainType(const raw::Identity &,
                         const TypeShape &) const override;
  llvm::Expected<OperationFacts>
  operation(const raw::Identity &, const OperationSignature &,
            const TypeTable &, const raw::Manifest &) const override;
  llvm::Error wire(const raw::Identity &, llvm::ArrayRef<NormalStatic>, TypeId,
                   const TypeTable &, const raw::Manifest &) const override;
  llvm::Error service(const raw::Identity &, const CapabilitySignature &,
                      const TypeTable &, const raw::Manifest &) const override;
  llvm::Error attributes(const raw::Identity &, llvm::ArrayRef<NormalStatic>,
                         const llvm::json::Value &) const override;
};

} // namespace zkc::mathematical
#endif
