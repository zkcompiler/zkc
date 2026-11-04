#ifndef ZKC_CONTRACTS_BINDINGS_H
#define ZKC_CONTRACTS_BINDINGS_H

#include "zkc/Contracts/Binding.h"
#include "zkc/Contracts/Generic.h"
#include <memory>
#include <variant>

namespace zkc::protocol {

struct TypeArgument;
struct VariantDescriptor;
class ImplementationCatalog;
/// Closed nominal type. Atomic constructors retain the compact identity slot;
/// an applied constructor instead owns kinded arguments and has no atomic
/// identity. Physical children are separate from logical static arguments.
struct BoundType {
  std::string kind, identity, representation;
  std::vector<TypeArgument> arguments = {};
  std::shared_ptr<const std::vector<BoundType>> physicalChildren = {};
  /// Variants own their nominal structure and ordered logical payloads. The
  /// atomic identity slot is empty; no encoded spelling is authoritative.
  std::shared_ptr<const VariantDescriptor> variant = {};
  bool operator==(const BoundType &other) const;
  bool operator!=(const BoundType &other) const { return !(*this == other); }
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

/// A nominal atom or an ordered tuple of nominal terms. Empty tuples are
/// meaningful; atoms must be nonempty UTF-8. Formation bounds expanded work.
struct VariantIdentity {
  using Tuple = std::vector<VariantIdentity>;
  std::variant<std::string, Tuple> value;
  VariantIdentity(std::string atom) : value(std::move(atom)) {}
  VariantIdentity(const char *atom) : value(std::string(atom)) {}
  VariantIdentity(Tuple tuple) : value(std::move(tuple)) {}
  const std::string *atom() const { return std::get_if<std::string>(&value); }
  const Tuple *tuple() const { return std::get_if<Tuple>(&value); }
  bool operator==(const VariantIdentity &other) const {
    return value == other.value;
  }
};
struct VariantAlternative {
  std::string label;
  std::vector<BoundType> payload;
  bool operator==(const VariantAlternative &other) const {
    return label == other.label && payload == other.payload;
  }
};
struct VariantDescriptor {
  VariantIdentity nominal;
  std::vector<VariantAlternative> alternatives;
  bool operator==(const VariantDescriptor &other) const {
    return nominal == other.nominal && alternatives == other.alternatives;
  }
};

/// Shared across structural arguments and variant payloads during admission.
struct TypeParseBudget {
  size_t remaining = 200000;
  size_t metadataRemaining = 64 * 1024 * 1024;
  bool limited = false;
  bool charge(size_t bytes) {
    if (bytes > metadataRemaining) {
      limited = true;
      return false;
    }
    metadataRemaining -= bytes;
    return true;
  }
  bool consume() {
    if (!remaining) {
      limited = true;
      return false;
    }
    --remaining;
    return true;
  }
};
llvm::Expected<BoundType> parseBoundType(llvm::StringRef spelling,
                                         bool physical, unsigned depth = 0,
                                         TypeParseBudget *budget = nullptr);
/// Validate actual structure, including caller-constructed values, without
/// a spelling round trip. Native structure and portable encoding have separate
/// allowances. A logical value has neither representation nor layout children.
llvm::Error checkBoundType(const BoundType &, bool physical,
                           TypeParseBudget *budget = nullptr,
                           unsigned depth = 0);
llvm::Expected<BoundType> variantType(VariantDescriptor);
/// Expanded nodes plus actual metadata bytes, or UINT64_MAX for malformed or
/// over-limit structure. This never builds a portable spelling.
uint64_t boundTypeWork(const BoundType &);
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
