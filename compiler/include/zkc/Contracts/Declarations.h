#ifndef ZKC_CONTRACTS_DECLARATIONS_H
#define ZKC_CONTRACTS_DECLARATIONS_H

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include <memory>
#include <optional>
#include <string>
#include <variant>
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
/// The setup-key role of a type constructor: its catalog row's `setup`.
inline std::optional<SetupKey> setupKey(llvm::StringRef constructor) {
  const auto *declared = typeDeclaration(constructor);
  return declared ? declared->setup : std::nullopt;
}
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

/// Source signature rules this frontend implements. The catalog's rule rows
/// declare each rule's shape. Presence grants no executable authority.
enum class FrontendSignature {
  RecordUnpack,
  RecordInspect,
  RecordRepack,
  RandomConstructor,
  NativeMessage
};
enum class SourceDeclarationKind {
  Math,
  Local,
  Interface,
  Requirement,
  ContractConstructor,
  View
};
/// A static parameter, optionally its associated member, or a parameterless
/// constructor.
struct SourceTerm {
  std::optional<unsigned> index;
  std::string member, constructor;
};
struct SourceStatic {
  std::string name, kind, sort;
};
struct SourceInput {
  std::string name;
  SourceTerm type;
};
enum class PatternSort { Contract, OptionalExtent };
struct UnsizedExtent {};
struct ExtentVariable {
  unsigned variable;
};
struct NatStatic {
  unsigned index;
};
using ExtentPattern = std::variant<UnsizedExtent, ExtentVariable, NatStatic>;
struct ContractPattern;
using PatternRef = std::shared_ptr<const ContractPattern>;
struct ContractVariable {
  unsigned variable;
};
struct ProductPattern {
  std::vector<PatternRef> elements;
};
struct SequencePattern {
  PatternRef element;
  ExtentPattern extent;
};
/// Installation-only patterns, never source Type binders or runtime values.
struct ContractPattern {
  std::variant<ContractVariable, ProductPattern, SequencePattern> value;
};
struct DescriptorPort {
  PatternRef contract;
};
struct SelectedViewPort {
  PatternRef context, state;
};
using SchemePort = std::variant<DescriptorPort, SelectedViewPort>;
struct NamedSchemePort {
  std::string name;
  SchemePort port;
};
enum class DescriptorForm {
  Append,
  Concat,
  Replace,
  ForgetExtent,
  CheckExtent,
  Fold
};
struct FrontendScheme {
  std::string name;
  DescriptorForm form;
  std::vector<PatternSort> variables;
  std::vector<StaticParameter> statics;
  std::vector<SchemePort> inputs;
  PatternRef output;
};
struct SchemeId {
  unsigned index;
};
struct ConcreteSourceSignature {
  std::vector<SourceStatic> statics;
  std::vector<SourceInput> inputs;
  std::optional<SourceTerm> output;
  std::optional<FrontendSignature> rule;
  std::string primitive;
};
struct InstalledContractHead {
  std::string constructor;
};
struct InstalledViewSignature {
  std::vector<SourceStatic> statics;
  std::vector<NamedSchemePort> inputs;
  PatternRef output;
  SchemeId scheme;
};
using InstalledSignature =
    std::variant<ConcreteSourceSignature, InstalledContractHead,
                 InstalledViewSignature>;
/// One exact installed signature alternative. Shells have no concrete callable
/// signature; consumers must select the typed alternative after index lookup.
struct FrontendDeclaration {
  std::string identity, module, name;
  SourceDeclarationKind kind;
  InstalledSignature signature;
  bool prelude;
  const ConcreteSourceSignature *concrete() const {
    return std::get_if<ConcreteSourceSignature>(&signature);
  }
  const InstalledContractHead *contractHead() const {
    return std::get_if<InstalledContractHead>(&signature);
  }
  const InstalledViewSignature *viewScheme() const {
    return std::get_if<InstalledViewSignature>(&signature);
  }
  std::optional<FrontendSignature> rule() const {
    auto *value = concrete();
    return value ? value->rule : std::nullopt;
  }
  llvm::ArrayRef<SourceStatic> statics() const {
    if (auto *value = concrete())
      return value->statics;
    if (auto *value = viewScheme())
      return value->statics;
    return {};
  }
};
llvm::ArrayRef<FrontendScheme> frontendSchemes();
const FrontendScheme *frontendScheme(SchemeId);
/// An installed notation of a declaration of its module. An empty fixity keeps
/// the symbol's fixed syntax.
struct FrontendNotation {
  std::string module, symbol, fixity;
  unsigned precedence;
  std::string target;
  bool isPublic;
};
/// Frontend-owned structural forms: logical oracle handles/sequences and
/// installed descriptor families. These forms have distinct value categories.
enum class FrontendConstructorForm {
  OracleHandle,
  OracleHandleSequence,
  FiniteDescriptor,
  DescriptorProduct,
  DescriptorSequence
};
/// A structural head the source language owns that is not a catalog data
/// constructor. The row owns the head's spelling; the frontend owns the
/// meaning of its form. Exactly one row spells each form.
struct FrontendConstructor {
  std::string name;
  FrontendConstructorForm form;
};
struct FrontendHome {
  std::string constructor, module;
  std::vector<std::string> members;
};
enum class ServiceSignature { RandomDraw, RandomIndex, RandomIndices };
struct ServiceMethodDeclaration {
  std::string identity, constructor, name;
  ServiceSignature signature;
  std::string capability;
};
llvm::ArrayRef<FrontendDeclaration> frontendDeclarations();
llvm::ArrayRef<FrontendNotation> frontendNotations();
/// The logical type heads the source language owns that are not catalog type
/// constructors. A frontend home names a catalog constructor or one of these.
llvm::ArrayRef<FrontendConstructor> frontendConstructors();
llvm::ArrayRef<FrontendHome> frontendHomes();
llvm::ArrayRef<ServiceMethodDeclaration> serviceMethodDeclarations();
const FrontendDeclaration *frontendDeclaration(llvm::StringRef qualifiedName);
/// The frontend constructor row with this spelling, if any.
const FrontendConstructor *frontendConstructor(llvm::StringRef spelling);

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
