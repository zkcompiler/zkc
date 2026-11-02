#ifndef ZKC_CONTRACTS_INSTANCES_H
#define ZKC_CONTRACTS_INSTANCES_H

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include <array>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

namespace zkc::protocol {
/// Generated installed-instance tables of the declaration catalog, in declared
/// order, checked by zkc-tblgen at build time. They declare which nominal
/// domains, logical type instances, codecs and frames exist; they grant no
/// execution, transport or implementation authority. The compiler's owners do
/// not read these tables: tests compare them with those owners.
namespace instances {
struct DomainMember {
  std::string member, identity;
};
struct ReductionTerm {
  unsigned exponent;
  std::string coefficient;
};
enum class ExtensionBase { BaseField, PrimeSubfield };
/// `B[X]/(X^degree - sum(c * X^e))` over the base the structure names.
struct FieldExtension {
  ExtensionBase over;
  unsigned degree;
  std::vector<ReductionTerm> reduction;
};
struct TwoAdicConvention {
  std::string convention, maximalRoot;
  unsigned twoAdicity;
  std::string ordering;
};
struct FieldFacts {
  std::string characteristic;
  /// Absent for a prime structure.
  std::optional<FieldExtension> extension;
  std::optional<TwoAdicConvention> twoAdic;
};
struct TranscriptFacts {
  std::string family;
  std::optional<std::string> hash;
  std::string decoder;
  bool bindsSuite;
};
enum class CommitmentScheme { Keccak256Rows, Poseidon2Rows, MultilinearKzg };
struct CommitmentFacts {
  CommitmentScheme scheme;
  std::optional<unsigned> digestBytes;
  std::optional<std::string> permutation;
  std::optional<unsigned> digestWordBytes;
};
struct Domain {
  std::string identity, sort;
  std::vector<DomainMember> members;
  std::vector<std::string> capabilities;
  std::optional<FieldFacts> field;
  std::optional<TranscriptFacts> transcript;
  std::optional<CommitmentFacts> commitment;
};
/// An empty domain denotes a nullary instance.
struct LogicalType {
  std::string kind, domain;
};
enum class FrameLayout {
  Scalar,
  Vector,
  SparseMatrix,
  MerkleRoot,
  MerklePath,
  DigestRoot,
  DigestProof,
  PcsCommitment,
  PcsProof,
  Table,
  Sequence,
  Variant,
  FieldArray
};
/// The codecs of `kind` over commitment domains of `scheme` share a tag.
struct SharedFrame {
  std::string kind;
  CommitmentScheme scheme;
};
struct FrameTag {
  unsigned tag;
  FrameLayout layout;
  std::optional<SharedFrame> shared;
};
struct CodecFrame {
  unsigned tag;
  std::optional<unsigned> elementBytes, bytes, bytesPerArity;
};
struct Codec {
  std::string identity, kind, domain;
  std::optional<CodecFrame> frame;
};
struct AggregateFrame {
  std::string constructor, domain;
  unsigned tag;
};
struct RandomService {
  std::string contract, field;
};
enum class LimitUnit { Roles, Bytes, Elements, Entries, Steps };
enum class LimitPhase { Formation, Admission, Publication, Execution };
struct Limit {
  std::string name;
  uint64_t value;
  LimitUnit unit;
  std::string owner, scope;
  LimitPhase phase;
};
enum class FiniteMode { Math, Local };
enum class FiniteOperation { Fold, Collect };
struct FiniteDefinition {
  std::string identity;
  FiniteMode mode;
  FiniteOperation operation;
  std::optional<std::string> collection;
  bool filtered;
};
enum class DomainConstructorKind {
  Elements,
  Indices,
  Range,
  Zip,
  Product,
  MatrixRow,
  MatrixColumn,
  MatrixCoordinates,
  SourceArray
};
struct DomainConstructor {
  std::string identity;
  DomainConstructorKind kind;
  unsigned axis;
};

llvm::ArrayRef<Domain> domains();
const Domain *domain(llvm::StringRef identity);
llvm::ArrayRef<LogicalType> logicalTypes();
llvm::ArrayRef<FrameTag> frameTags();
const FrameTag *frameTag(unsigned tag);
llvm::ArrayRef<Codec> codecs();
const Codec *codec(llvm::StringRef identity);
llvm::ArrayRef<AggregateFrame> aggregateFrames();
llvm::ArrayRef<RandomService> randomServices();
llvm::ArrayRef<Limit> limits();
const Limit *limit(llvm::StringRef name);
llvm::ArrayRef<FiniteDefinition> finiteDefinitions();
llvm::ArrayRef<DomainConstructor> domainConstructors();

/// Shared ceiling values, usable in constant expressions.
struct LimitValue {
  std::string_view name;
  uint64_t value;
};
#define ZKC_INSTALLED_LIMIT_VALUES
#include "zkc/Contracts/Instances.inc"
constexpr std::optional<uint64_t> limitValue(std::string_view name) {
  for (const auto &row : limitValues)
    if (row.name == name)
      return row.value;
  return std::nullopt;
}
/// The ordered role roster of one protocol, participant or Entry, and the role
/// telescope of one distributed record, enforced at admission.
inline constexpr uint64_t protocolRoleLimit =
    limitValue("protocol.roles").value();
} // namespace instances

/// Generated native installation tables: available physical choices, in
/// declared order. A provider preference is not an installation grant, and
/// a target still admits each exact handler, signature and storage owner.
namespace installation {
enum class ValueFrame { Canonical, Local };
struct Representation {
  std::string identity, kind, domain;
  bool isDefault;
  std::string layout;
  ValueFrame frame;
  std::string unit;
};
struct TypeTreeArgument;
/// A logical type tree in an exact type pattern: a constructor application.
struct TypeTree {
  std::string constructor;
  std::vector<TypeTreeArgument> arguments;
};
struct TypeTreeArgument {
  enum class Kind { Domain, Type, Nat };
  Kind kind;
  std::string sort, identity;
  std::optional<TypeTree> type;
  std::string natural;
};
struct ArgumentPattern {
  enum class Kind { Domain, Type, NatRange, Any };
  Kind kind;
  std::string sort, identity;
  std::optional<TypeTree> type;
  uint64_t minimum, maximum;
};
struct RepresentationChild {
  std::string kind, domain, representation;
};
struct AppliedRepresentation {
  std::string constructor;
  std::vector<ArgumentPattern> arguments;
  std::string identity;
  bool isDefault;
  std::optional<RepresentationChild> child;
  ValueFrame frame;
  std::string unit;
};
struct Provider {
  std::string domain, defaultProvider;
  std::vector<std::string> alternatives;
};
struct ProviderUnit {
  std::string provider, unit;
};
struct ResidueArithmetic {
  std::string form, representation;
};
struct MontgomeryForm {
  unsigned wordBytes, radixBits;
};
struct ByteEncoding {
  std::string codec, order;
};
struct FieldForm {
  std::string field;
  std::optional<ResidueArithmetic> arithmetic;
  std::optional<MontgomeryForm> montgomery;
  std::optional<ByteEncoding> byteEncoding;
};
/// A backend calling convention, not part of the logical declaration.
struct PhysicalArguments {
  std::string operation;
};

llvm::ArrayRef<Representation> representations();
llvm::ArrayRef<AppliedRepresentation> appliedRepresentations();
llvm::ArrayRef<Provider> providers();
const Provider *provider(llvm::StringRef domain);
llvm::ArrayRef<ProviderUnit> providerUnits();
llvm::StringRef providerUnit(llvm::StringRef provider);
llvm::ArrayRef<FieldForm> fieldForms();
const FieldForm *fieldForm(llvm::StringRef field);
llvm::ArrayRef<PhysicalArguments> physicalArguments();
} // namespace installation
} // namespace zkc::protocol
#endif
