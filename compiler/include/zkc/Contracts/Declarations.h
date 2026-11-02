#ifndef ZKC_CONTRACTS_DECLARATIONS_H
#define ZKC_CONTRACTS_DECLARATIONS_H

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include <optional>
#include <string>
#include <vector>

namespace zkc::protocol {
enum class StaticKind { Domain, Type, Nat };
struct StaticParameter {
  StaticKind kind;
  /// Only Domain parameters carry an installed sort name.
  std::string sort;
  bool operator==(const StaticParameter &other) const {
    return kind == other.kind && sort == other.sort;
  }
};
struct CapabilityDeclaration {
  std::string name;
  std::vector<StaticParameter> parameters;
};
struct AssociatedMemberDeclaration {
  std::string name;
  StaticParameter owner, result;
};
/// The element of a source collection: the value type of the first parameter,
/// an index, or a byte.
enum class CollectionElement { Parameter, Index, Byte };
struct TypeCollection {
  unsigned rank;
  CollectionElement element;
};
enum class SetupKey { Prover, Verifier };
struct TypeDeclaration {
  std::string name;
  std::vector<StaticParameter> parameters;
  bool nativeLocal, mathematical, participants, constructible, message;
  /// Source vocabulary: native source data, the collection view and the
  /// setup-key role. These grant no codec, transport or execution authority.
  bool sourceData = false;
  std::optional<TypeCollection> collection = {};
  std::optional<SetupKey> setup = {};
};
llvm::ArrayRef<TypeDeclaration> typeDeclarations();
const TypeDeclaration *typeDeclaration(llvm::StringRef name);
llvm::ArrayRef<std::string> domainSorts();
llvm::ArrayRef<CapabilityDeclaration> capabilityDeclarations();
llvm::ArrayRef<AssociatedMemberDeclaration> associatedMemberDeclarations();

enum class AuthoringStage { Source, Construction, CompilerGenerated, Physical };
/// Unknown contracts are CompilerGenerated, and never source authorable.
AuthoringStage authoringStage(llvm::StringRef contract);

struct SourceTypeExport {
  std::string module, name, constructor;
};
/// A finite source type family reduces after its element head is known.
/// It does not introduce a new common logical constructor.
struct SourceTypeFamilyCase {
  std::string family, elementConstructor, resultConstructor;
};
struct SourceAssociatedType {
  std::string sort, member, constructor;
};
struct SourceCapabilityExport {
  std::string module, name, predicate;
};
llvm::ArrayRef<SourceTypeFamilyCase> sourceTypeFamilies();
llvm::ArrayRef<SourceAssociatedType> sourceAssociatedTypes();
llvm::ArrayRef<SourceCapabilityExport> sourceCapabilityExports();
llvm::ArrayRef<SourceTypeExport> sourceTypeExports();

/// Closed source signature rules. Presence grants no executable authority.
enum class FrontendSignature {
  RecordUnpack,
  RecordInspect,
  RecordRepack,
  RandomConstructor
};
struct FrontendAssociation {
  std::string identity, module, name;
  FrontendSignature signature;
  bool implicit;
};
struct FrontendHome {
  std::string constructor, module;
  std::vector<std::string> members;
};
enum class ServiceSignature { RandomDraw, RandomIndex, RandomIndices };
struct ServiceMethodDeclaration {
  std::string name;
  ServiceSignature signature;
  std::string capability;
};
llvm::ArrayRef<FrontendAssociation> frontendAssociations();
llvm::ArrayRef<FrontendHome> frontendHomes();
llvm::ArrayRef<ServiceMethodDeclaration> serviceMethodDeclarations();
const FrontendAssociation *frontendAssociation(llvm::StringRef qualifiedName);

enum class Custody { Unknown, PublicValue, PrivateImmutable, Affine };
struct TypePermissions {
  bool copy, drop;
  Custody custody;
};
/// Constructor permissions only; formation and variant recursion are separate.
const TypePermissions *typePermissions(llvm::StringRef constructor);

enum class ParameterValidator {
  None,
  Natural,
  Extent,
  FieldLiteral,
  FieldLiterals,
  MatrixShape,
  MatrixIdentity,
  AssetIdentity,
  MatrixVector,
  GatherIndices,
  ScatterIndices,
  NativeOrigin,
  NativeIndexBlock,
  NumericalExpression
};
struct ParameterContract {
  ParameterValidator validator;
  unsigned minimum;
  std::optional<unsigned> maximum;
  /// Scoped Field term used by literal validation; not a root argument index.
  std::optional<unsigned> fieldTerm = {};
  /// Canonical mathematical carrier named by an AssetIdentity parameter.
  /// Empty for parameter contracts that do not refer to captured assets.
  llvm::StringRef assetFormat = {};
};
const ParameterContract *parameterContract(llvm::StringRef contract);

enum class ConsumerImplementation { Unselected };
struct ConsumerProfileOperation {
  std::string operation;
  /// Formal roots in scope order, excluding projections and constants.
  std::vector<StaticParameter> staticParameters;
};
struct ConsumerProfile {
  std::string name;
  ConsumerImplementation implementation;
  std::vector<std::string> typeConstructors;
  std::vector<ParameterValidator> parameterValidators;
  std::vector<ConsumerProfileOperation> operations;
};
/// Owner-fixed selections; declaration/contribution presence never enrolls an
/// operation. Generation checks each entry against its exact declaration.
llvm::ArrayRef<ConsumerProfile> consumerProfiles();
const ConsumerProfile *consumerProfile(llvm::StringRef name);
/// Null for an unknown profile or nonmember. Membership grants no execution,
/// interpretation, domain, implementation or actual-argument admission.
const ConsumerProfileOperation *
consumerProfileOperation(llvm::StringRef profile, llvm::StringRef operation);
} // namespace zkc::protocol
#endif
