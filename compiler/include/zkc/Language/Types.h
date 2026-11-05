#ifndef ZKC_LANGUAGE_TYPES_H
#define ZKC_LANGUAGE_TYPES_H
#include "zkc/Language/Natural.h"
#include "zkc/Language/ValuePlacement.h"
#include <optional>
#include <string>
#include <vector>

namespace zkc::language {
/// Authored resource restrictions. Ordinary declarations derive their usage
/// properties from their representation instead.
enum class Resource { Affine, Linear };
struct Permissions {
  bool copy = false, drop = false;
  bool operator==(const Permissions &b) const {
    return copy == b.copy && drop == b.drop;
  }
  bool includes(const Permissions &b) const {
    return (!b.copy || copy) && (!b.drop || drop);
  }
};
/// A resolved source term. Natural, Domain, Asset and Module are static
/// sorts and cannot form runtime values. Parameters carry
/// declaration-qualified atom identities. Nominal arguments include phantom
/// parameters; representation is not identity.
enum class DescriptorFamily { Finite };

struct Type {
  enum class Kind {
    Boolean,
    Field,
    Group,
    Index,
    Unit,
    Tuple,
    Array,
    Record,
    Variant,
    Parameter,
    Associated,
    Natural,
    Module,
    Builtin,
    Formal,
    Domain,
    /// A capture-local immutable asset (a ring arena or a relation bundle).
    /// The domain is the canonical asset identity when closed and the
    /// parameter atom when symbolic; the sort is Ring or Bundle.
    Asset,
    /// A static logical oracle kind, independent of installed native domains.
    OracleKind,
    /// Role-family values eliminated by semantic realization before execution.
    Oracle,
    OracleSequence,
    /// A forward association of a symbolic logical kind; never an injective
    /// constructor.
    OracleProjection,
    /// A nominal protocol product whose fields have independent placements.
    LogicalRecord,
    /// Installed structural family; never an ordinary Type argument or value.
    Descriptor,
    /// Ordered concrete descriptor contracts, including zero or one child.
    DescriptorProduct,
    /// One concrete descriptor child, then an optional typed natural extent.
    /// Absence denotes a bounded finite payload whose length is not identity.
    DescriptorSequence
  };
  Kind kind = Kind::Boolean;
  DescriptorFamily family = DescriptorFamily::Finite;
  std::string domain;
  /// Catalog sort for static-only domains and asset sort for assets; Field and
  /// Group use their own kinds.
  std::string sort;
  std::vector<Type> arguments;
  Natural dimension;
  bool symbolic = false;
  Permissions assumptions;
  Type() = default;
  Type(Kind kind, std::string domain = {})
      : kind(kind), domain(std::move(domain)) {}
  bool operator==(const Type &b) const {
    if (kind == Kind::Natural && b.kind == Kind::Natural)
      return dimension == b.dimension;
    return kind == b.kind && (kind != Kind::Descriptor || family == b.family) &&
           domain == b.domain && sort == b.sort && arguments == b.arguments &&
           dimension == b.dimension && symbolic == b.symbolic;
  }
  bool operator!=(const Type &b) const { return !(*this == b); }
};
/// Type identity and participant placement are separate judgments. Absence of
/// placement denotes an ordinary unplaced mathematical/local context.
struct PlacedType {
  Type type;
  std::optional<ValuePlacement> placement = {};
  bool operator==(const PlacedType &other) const {
    return type == other.type && placement == other.placement;
  }
  bool operator!=(const PlacedType &other) const { return !(*this == other); }
};
/// Canonical source term for an admitted catalog domain sort and identity.
/// Only this constructor and assetType set Type::sort.
Type domainType(llvm::StringRef sort, llvm::StringRef identity);
llvm::StringRef domainSort(const Type &);
/// Asset sorts name captured mathematics, never installed catalog identities.
bool isAssetSort(llvm::StringRef);
/// Canonical source term for a captured asset of the given sort. The identity
/// is the canonical definition identity of the captured asset.
Type assetType(llvm::StringRef sort, llvm::StringRef identity);
/// The asset sort of an asset term; empty for every other kind.
llvm::StringRef assetSort(const Type &);
bool isStaticOnly(const Type &);
bool isDescriptor(const Type &);
/// Typed signature contract, independent of the callable mode.
struct DescriptorContract {
  /// Candidate representation, not admission evidence. Structural forms use
  /// dedicated kinds, never installed leaf-family identities or data kinds.
  Type type = Type(Type::Kind::Descriptor);
  DescriptorContract() = default;
  DescriptorContract(DescriptorFamily family, std::vector<Type> parameters)
      : type(Type::Kind::Descriptor) {
    type.family = family;
    type.arguments = std::move(parameters);
  }
  explicit DescriptorContract(Type type) : type(std::move(type)) {}
  bool operator==(const DescriptorContract &other) const {
    return type == other.type;
  }
  bool operator!=(const DescriptorContract &other) const {
    return !(*this == other);
  }
};
/// Candidate projection only. Admission/replay must bound and validate before
/// copying an untrusted term; a successful projection grants no authority.
std::optional<DescriptorContract> descriptorContract(const Type &);
/// Borrow the sole representation; no recursive copy or parallel walk engine.
const Type &descriptorType(const DescriptorContract &);
/// Finite interpretation only: reject every other family and incorrect arity.
const Type *finiteDescriptorItem(const DescriptorContract &);
/// Direct logical handle values; aggregate formation has its own recursive
/// check.
bool isOracleHandle(const Type &);
/// Logical handles, nominal distributed records and their finite structural
/// products. This category check does not depend on represented storage.
bool isLogicalValue(const Type &);
/// Placed category also recognizes a heterogeneous ordinary tuple/array.
/// Its unplaced Type retains the ordinary structural/static identity.
bool isLogicalValue(const PlacedType &);
/// Library constructor spelling, distinct from native-data eligibility.
llvm::StringRef oracleConstructor(const Type &);
/// Exact installed form's spelling for a logical head or descriptor family.
llvm::StringRef frontendTypeConstructor(const Type &);
llvm::StringRef typeKindName(Type::Kind);
std::string spelling(const Type &);
/// Injective lookup key within one checked snapshot; source-facing spelling is
/// deliberately separate. It binds no source revision, so it never decides
/// nominal equality across captures.
/// Callers precharge typeComplexity before copying keys of candidate terms;
/// this unchecked snapshot helper itself never establishes admission.
std::string typeIdentity(const Type &);
/// The defining authority of a nominal declaration path: 64 lowercase hex
/// for an authored or installed declaration, none for a generated one.
using NominalAuthority =
    llvm::function_ref<llvm::Expected<std::optional<std::string>>(
        llvm::StringRef path)>;
/// Revision-bound nominal key. It frames exactly as typeIdentity and adds one
/// frame after the domain of every Record, LogicalRecord, Variant and Module
/// node that names a declaration: that path's defining authority, or an empty
/// frame for a generated declaration. A symbolic module parameter names no
/// declaration and adds no frame. Associated nodes are bound through their
/// module argument.
/// Enforces default candidate depth/node/identity-work ceilings itself;
/// ledger-owning callers additionally precharge their remaining allowance.
llvm::Expected<std::string> canonicalTypeKey(const Type &, NominalAuthority);
/// Bound traversal, candidate descriptor shapes and the selected operation
/// before copying a term or constructing its expanded identity. An optional
/// ordinary static replacement borrows a
/// complete selected term; its contents are not substituted a second time.
using TypeReplacement = llvm::function_ref<const Type *(const Type &)>;
enum class TypeWork { Copy, Identity };
llvm::Expected<uint64_t>
typeComplexity(const Type &, uint64_t nodes, uint64_t depth,
               uint64_t work = UINT64_MAX, TypeReplacement = nullptr,
               bool complete = true, TypeWork = TypeWork::Identity);
} // namespace zkc::language
#endif
