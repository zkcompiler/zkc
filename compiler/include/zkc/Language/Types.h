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
    Descriptor
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
  DescriptorFamily family;
  std::vector<Type> parameters;
  bool operator==(const DescriptorContract &other) const {
    return family == other.family && parameters == other.parameters;
  }
  bool operator!=(const DescriptorContract &other) const {
    return !(*this == other);
  }
};
std::optional<DescriptorContract> descriptorContract(const Type &);
/// Lossless projection into the existing typed static term traversal.
Type descriptorType(const DescriptorContract &);
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
llvm::Expected<std::string> canonicalTypeKey(const Type &, NominalAuthority);
/// Bound traversal and expanded identity material before copying a term.
llvm::Expected<uint64_t> typeComplexity(const Type &, uint64_t nodes,
                                        uint64_t depth);
} // namespace zkc::language
#endif
