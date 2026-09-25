#ifndef ZKC_PROTOCOL_BINDINGS_H
#define ZKC_PROTOCOL_BINDINGS_H

#include "mlir/IR/Types.h"
#include "zkc/Compiler/Generic.h"
#include "zkc/Source/Model.h"

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
mlir::Type decodeBoundType(mlir::MLIRContext *, const BoundType &);
llvm::Expected<BoundType> encodeBoundType(mlir::Type, bool physical);
llvm::Expected<BoundType> defaultRepresentation(const BoundType &logical);

struct BoundOperation {
  std::string operation;
  std::vector<BoundType> inputs, outputs;
};

/// Independently installed logical contract and physical implementation tables
/// determine exact signatures. Serialized bindings do not declare new facts.
llvm::Expected<BoundOperation> resolveBinding(const source::OperationBinding &,
                                              bool physical);
/// Shared declaration validation for typed source, MLIR, and encoded inputs.
llvm::Error checkBindingDeclaration(const source::OperationBinding &,
                                    bool physical);
llvm::Expected<source::OperationBinding>
readBinding(mlir::Operation *declaration);
llvm::Expected<source::OperationBinding>
operationBinding(mlir::Operation *user);
mlir::LogicalResult verifyBoundOperation(mlir::Operation *, bool physical);
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
llvm::Expected<std::string>
defaultImplementation(const source::OperationBinding &);
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
