#ifndef ZKC_CONTRACTS_BINDINGS_H
#define ZKC_CONTRACTS_BINDINGS_H

#include "zkc/Contracts/Binding.h"
#include "zkc/Contracts/Generic.h"
#include <memory>

namespace zkc::protocol {

struct TypeArgument;
class ImplementationCatalog;
/// Closed nominal type. Atomic constructors retain the compact identity slot;
/// an applied constructor instead owns kinded arguments and has no atomic
/// identity. Physical children are separate from logical static arguments.
struct BoundType {
  std::string kind, identity, representation;
  std::vector<TypeArgument> arguments = {};
  std::shared_ptr<const std::vector<BoundType>> physicalChildren = {};
  bool operator==(const BoundType &other) const;
  std::string spelling() const;
};

struct TypeArgument {
  enum class Kind { Domain, Type, Nat };
  Kind kind;
  std::string domain;
  std::shared_ptr<const BoundType> type;
  uint64_t natural = 0;
  static TypeArgument domainArgument(std::string identity);
  static TypeArgument typeArgument(BoundType type);
  static TypeArgument naturalArgument(uint64_t value);
  bool operator==(const TypeArgument &other) const;
  std::string spelling() const;
};

/// Shared across structural arguments and variant payloads during admission.
struct TypeParseBudget {
  size_t remaining = 200000;
  size_t metadataRemaining = 64 * 1024 * 1024;
  bool charge(size_t bytes) {
    if (bytes > metadataRemaining)
      return false;
    metadataRemaining -= bytes;
    return true;
  }
  bool consume() {
    if (!remaining)
      return false;
    --remaining;
    return true;
  }
};
llvm::Expected<BoundType> parseBoundType(llvm::StringRef spelling,
                                         bool physical, unsigned depth = 0,
                                         TypeParseBudget *budget = nullptr);
/// Syntactic head and immediate arguments; arguments may name scoped statics.
/// Does not confer closed admission or capability facts.
struct TypeApplication {
  std::string constructor;
  std::vector<std::string> arguments;
};
llvm::Expected<TypeApplication> splitTypeApplication(llvm::StringRef spelling);
/// Ground structural application formation. Atomic constructors use their
/// canonical compact shape; argument kinds are owned by declarations.
llvm::Expected<BoundType> applyBoundType(llvm::StringRef constructor,
                                         llvm::ArrayRef<std::string> arguments);
llvm::Expected<BoundType> defaultRepresentation(const BoundType &logical);

inline constexpr size_t PhysicalSpellingBytes = 1024 * 1024;
BoundType erasePhysicalType(const BoundType &);
llvm::Expected<std::vector<BoundType>> logicalChildren(const BoundType &);
llvm::Expected<BoundType> physicalType(const BoundType &logical,
                                       llvm::StringRef representation,
                                       std::vector<BoundType> children);

struct BoundOperation {
  std::vector<BoundType> inputs, outputs;
};

/// Resolve only logical signatures and requirements. The caller retains the
/// original implementation constraint; this query grants no physical admission.
llvm::Expected<BoundOperation>
resolveLogicalBinding(const BindingApplication &binding);
/// Independently installed declarations and implementations determine exact
/// signatures. The overload admits against an explicit immutable installation.
llvm::Expected<BoundOperation> resolveBinding(const BindingApplication &,
                                              bool physical,
                                              const ImplementationCatalog &);
llvm::Expected<BoundOperation> resolveBinding(const BindingApplication &,
                                              bool physical);
/// Independent neutral declaration validation for source/model and byte
/// boundaries. Native MLIR admission uses its typed installation checker.
llvm::Error checkBindingDeclaration(llvm::StringRef name,
                                    const BindingApplication &, bool physical);
/// Static library declarations use the same operation contracts. Bodies are
/// checked before any nominal domain or implementation is selected.
llvm::ArrayRef<generic::TypeConstructor> boundTypeConstructors();
/// All declarations, including explicit variable-signature families. Presence
/// does not select a consumer profile or grant source authoring.
llvm::ArrayRef<generic::Operation> executableOperationContracts();
llvm::ArrayRef<requirements::Implication> boundCapabilityRules();
llvm::StringRef installedIdentitySort(llvm::StringRef identity);
/// Formation of a ground static, using the reserved Type/Nat kind tokens.
bool staticIdentityMatches(llvm::StringRef sort, llvm::StringRef identity);
llvm::StringRef associatedIdentity(llvm::StringRef identity,
                                   llvm::StringRef member);
/// Canonical installed wire codec for a complete logical payload type. Empty
/// means that the registry offers no default; it never guesses from a kind
/// alone.
llvm::StringRef defaultCodec(const BoundType &logical);
llvm::Error checkStaticVocabulary(const generic::Signature &);
/// Choose the installed dense backend without changing logical ports.
llvm::Expected<std::string> defaultImplementation(const BindingApplication &);
/// True only for installed depth-one local contraction representations.
bool isDiagonalRepresentation(llvm::StringRef representation);
llvm::Error checkImplementation(llvm::StringRef contract,
                                llvm::StringRef implementation);
llvm::StringRef associatedMemberSort(llvm::StringRef sort,
                                     llvm::StringRef member);
llvm::Expected<std::vector<std::string>>
resolveStaticArguments(const generic::Scope &, llvm::ArrayRef<std::string>);
llvm::Error checkClosedRequirements(llvm::ArrayRef<requirements::Predicate>,
                                    llvm::ArrayRef<std::string> identities);

} // namespace zkc::protocol

#endif
