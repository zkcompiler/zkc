#ifndef ZKC_MATHEMATICAL_REGISTRY_H
#define ZKC_MATHEMATICAL_REGISTRY_H

#include "zkc/Mathematical/Types.h"

namespace zkc::mathematical {

struct CapabilitySignature {
  uint32_t service;
  std::vector<NormalStatic> statics;
  std::vector<TypeId> arguments;
  TypeId result;
  bool operator==(const CapabilitySignature &other) const;
};
struct OperationSignature {
  std::vector<NormalStatic> parameters;
  std::vector<CapabilitySignature> capabilities;
  std::vector<TypeId> arguments;
  TypeId result;
};
struct OperationFacts {
  protocol::OperationPurity purity;
  /// Required inequality of resolved capability roots, never of reply values.
  std::vector<std::pair<uint64_t, uint64_t>> distinct;
};

/// Conservative reuse of the existing installed nominal-domain catalog. The
/// caller first resolves and pins its mathematical package, then explicitly
/// selects the catalog identity. Only closed unary nominal value constructors
/// and mathematical polynomial/residual families over registered fields are
/// covered. Resources, representations and operation purity are not imported.
llvm::Error checkInstalledDomainType(llvm::StringRef nominalIdentity,
                                     const TypeShape &);

/// An explicit semantic installation supplied by the consumer. Implementations
/// resolve actual packages and compare exact signatures against their own
/// declarations, including prerequisites and attribute schemas. There is no
/// permissive default. A digest or an authored purity label grants no fact.
///
/// The native implementation is a trust boundary. Independent Lean admission
/// selects its own registered interpretation; a native callback is not a proof.
class Registry {
public:
  enum class Category { Domain, Operation, Wire, Service, Law };
  virtual ~Registry() = default;
  virtual llvm::Error identity(Category, const raw::Identity &,
                               const raw::Manifest &) const = 0;
  virtual llvm::Error domainType(const raw::Identity &,
                                 const TypeShape &) const = 0;
  virtual llvm::Expected<OperationFacts>
  operation(const raw::Identity &, const OperationSignature &,
            const TypeTable &, const raw::Manifest &) const = 0;
  virtual llvm::Error wire(const raw::Identity &, llvm::ArrayRef<NormalStatic>,
                           TypeId, const TypeTable &,
                           const raw::Manifest &) const = 0;
  virtual llvm::Error service(const raw::Identity &,
                              const CapabilitySignature &, const TypeTable &,
                              const raw::Manifest &) const = 0;
  virtual llvm::Error attributes(const raw::Identity &,
                                 llvm::ArrayRef<NormalStatic>,
                                 const llvm::json::Value &) const = 0;
};

} // namespace zkc::mathematical
#endif
