#ifndef ZKC_CONTRACTS_BINDINGS_H
#define ZKC_CONTRACTS_BINDINGS_H

#include "zkc/Contracts/Binding.h"
#include "zkc/Contracts/Generic.h"

namespace zkc::protocol {

/// Closed nominal type. Representation is empty at logical stages. The wire
/// encoding is kind:identity@representation (bool has no identity).
struct BoundType {
  std::string kind, identity, representation;
  bool operator==(const BoundType &other) const;
  std::string spelling() const;
};

llvm::Expected<BoundType> parseBoundType(llvm::StringRef spelling,
                                         bool physical);
llvm::Expected<BoundType> defaultRepresentation(const BoundType &logical);

struct BoundOperation {
  std::vector<BoundType> inputs, outputs;
};

/// Independently installed logical contract and physical implementation tables
/// determine exact signatures. Serialized bindings do not declare new facts.
llvm::Expected<BoundOperation> resolveBinding(const BindingApplication &,
                                              bool physical);
/// Shared declaration validation for typed source, MLIR, and encoded inputs.
llvm::Error checkBindingDeclaration(llvm::StringRef name,
                                    const BindingApplication &, bool physical);
/// Static library declarations use the same operation contracts. Bodies are
/// checked before any nominal domain or implementation is selected.
llvm::ArrayRef<generic::TypeConstructor> boundTypeConstructors();
llvm::ArrayRef<generic::Operation> boundOperationContracts();
llvm::ArrayRef<requirements::Implication> boundCapabilityRules();
llvm::StringRef installedIdentitySort(llvm::StringRef identity);
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
