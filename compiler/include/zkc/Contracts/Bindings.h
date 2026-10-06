#ifndef ZKC_CONTRACTS_BINDINGS_H
#define ZKC_CONTRACTS_BINDINGS_H

#include "zkc/Contracts/Binding.h"
#include "zkc/Contracts/Generic.h"
#include <memory>

namespace zkc::protocol {

struct TypeArgument;
/// Closed nominal type. Atomic constructors retain the compact identity slot;
/// an applied constructor instead owns kinded arguments and has no atomic
/// identity. Representation belongs only to the outer physical value.
struct BoundType {
  std::string kind, identity, representation;
  std::vector<TypeArgument> arguments = {};
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
/// Construction-only complete-type bindings are not common generic operations.
llvm::ArrayRef<generic::Operation> nonGenericOperationContracts();
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
