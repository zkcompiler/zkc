#ifndef ZKC_LANGUAGE_LAYOUT_H
#define ZKC_LANGUAGE_LAYOUT_H
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/OracleKinds.h"
#include "zkc/Language/Project.h"
#include <map>
#include <variant>
namespace zkc::language {
namespace detail {
class Semantics;
struct CheckedStorage;
/// The nominal authorities a semantic view lays out with. Checking builds
/// carriers before authorities are final, so its view is provisional: each
/// authored or installed frame is 64 '-' bytes and a generated frame is empty,
/// so every byte-limit decision equals the final one. Only a view over a
/// finalized checked project publishes identities.
struct AuthorityView {
  /// The finalized checked project; null for the provisional view.
  const CheckedStorage *final = nullptr;
};
} // namespace detail
struct PolynomialLayout {
  std::string field;
  uint64_t arity;
};
struct QuotientLayout {
  uint64_t modulus;
  uint64_t degree;
};
struct OracleKindLayout {
  std::string identity;
  std::vector<protocol::TypeArgument> arguments;
  protocol::OracleKindSignature signature;
};
struct OracleLayout {
  OracleKindLayout kind;
  /// Present only for a bounded sequence, including the zero maximum.
  std::optional<uint64_t> maximum;
};
/// One mathematical SSA leaf: executable native data or a formal algebraic
/// value or logical handle. The variant prevents passing either as a BoundType
/// string.
class LayoutLeaf {
public:
  LayoutLeaf(protocol::BoundType data) : value(std::move(data)) {}
  LayoutLeaf(PolynomialLayout polynomial) : value(std::move(polynomial)) {}
  LayoutLeaf(QuotientLayout quotient) : value(quotient) {}
  LayoutLeaf(OracleLayout oracle) : value(std::move(oracle)) {}
  const OracleLayout *oracle() const {
    return std::get_if<OracleLayout>(&value);
  }
  const protocol::BoundType *data() const {
    return std::get_if<protocol::BoundType>(&value);
  }
  const PolynomialLayout *polynomial() const {
    return std::get_if<PolynomialLayout>(&value);
  }
  const QuotientLayout *quotient() const {
    return std::get_if<QuotientLayout>(&value);
  }
  uint64_t cost() const {
    if (const auto *logical = oracle()) {
      auto work = protocol::boundTypeWork(logical->kind.signature.answer);
      return work > UINT64_MAX - 8 ? UINT64_MAX : work + 8;
    }
    return data()         ? protocol::boundTypeWork(*data())
           : polynomial() ? polynomial()->field.size() + 2
                          : 3;
  }

private:
  std::variant<protocol::BoundType, PolynomialLayout, QuotientLayout,
               OracleLayout>
      value;
};
struct Layout;
struct LayoutField {
  std::string name;
  std::shared_ptr<const Layout> layout;
  unsigned offset = 0;
  /// Row bound of this direct logical field, after generic substitution.
  std::optional<uint64_t> maximumRows = {};
  bool isPublic = true;
  /// Specialized formula in this declaration's ordered role telescope.
  std::optional<ValuePlacement> placement = {};
};
struct LayoutAlternative {
  std::string name;
  std::vector<LayoutField> fields;
};
/// Revision-bound nominal identity of one closed type.
struct LayoutIdentity {
  /// canonicalTypeKey over the owning view's authorities.
  std::string key;
  /// Lowercase SHA-256 hex of key: the published schema identity.
  std::string digest;
};
/// A logical source value has one deterministic, bounded SSA layout.
/// Products flatten in declaration order; variants retain their closed tag.
/// Custody, when present, is a prefix and is never a user data field.
struct Layout {
  Type type;
  /// Set once when the layout is built. Custody slots, nominal preimages and
  /// published schemas use it; in-snapshot lookups keep typeIdentity.
  LayoutIdentity identity;
  /// Generated nominal identity binds exact source, family and installation.
  std::string generatedIdentity;
  Permissions permissions;
  std::vector<std::string> roleParameters;
  std::optional<Resource> restriction = {};
  bool sealed = false;
  std::vector<LayoutLeaf> leaves;
  std::vector<LayoutField> fields;
  std::vector<LayoutAlternative> alternatives;
  bool custody = false;
  /// One unit for an ordinary restriction; telescope arity for a distributed
  /// one.
  unsigned custodyCount = 0;
  /// Retained even for zero arrays, independently of physical fields.
  std::shared_ptr<const Layout> element;
  bool constructible = false;
  /// Includes formal element meaning even when an array has zero leaves.
  bool formal = false;
  /// Kind-associated data schema of a direct handle or sequence. Logical
  /// record roots have no aggregate oracle data schema.
  std::shared_ptr<const Layout> oracleData;
};
/// Full logical schemas, including nominal identity and member names, are
/// significant across captures. Cache only within an immutable layout phase:
/// the memo is keyed by layout address, so it never outlives the Layouts that
/// owns those layouts.
class LayoutIdentities {
  uint64_t &remaining;
  std::map<const Layout *, std::string> cache;
  unsigned depth = 0;

public:
  explicit LayoutIdentities(uint64_t &remaining) : remaining(remaining) {}
  llvm::Expected<std::string> get(const Layout &);
};
struct LayoutSlice {
  unsigned offset;
  std::shared_ptr<const Layout> layout;
};
/// One body leaf and its declaration-ordered protocol ABI expansion. Paths
/// index source fields, including private fields; they grant no access rights.
struct ProtocolPortLeaf {
  LayoutLeaf leaf;
  unsigned bodyOffset = 0, nativeOffset = 0;
  std::vector<unsigned> path;
  /// Present for a handle or sequence; never for an aggregate root.
  std::shared_ptr<const Layout> oracleData;
  std::optional<uint64_t> maximumRows = {};
  std::optional<ValuePlacement> placement = {};
  bool custody = false;
  unsigned nativeSize() const { return leaf.oracle() ? 2 : 1; }
  /// Body availability only; never a field-access or common-value judgment.
  std::vector<unsigned> roles() const;
};
enum class ProtocolComponentFacet { Data, OracleData, OracleAnchor, Custody };
/// Component identity is typed and independent of the physical SSA selection.
struct ProtocolPortComponent {
  std::vector<unsigned> fieldPath;
  unsigned localLeaf;
  unsigned role;
  ProtocolComponentFacet facet;
  unsigned nativeIndex;
};
/// A bounded observation of a source layout, not an executable representation.
/// Each handle expands to its own holder data and exact receiver anchor family.
/// Multiple ordinary components can deliberately select the same native index.
struct ProtocolPortLayout {
  std::shared_ptr<const Layout> body;
  std::vector<ProtocolPortLeaf> leaves;
  /// Prefix map from body offsets (including the end) to ABI offsets.
  std::vector<unsigned> nativeOffsets{0};
  std::optional<ValuePlacement> placement = {};
  std::vector<ProtocolPortComponent> components;
  unsigned size() const { return nativeOffsets.back(); }
  llvm::Expected<LayoutSlice> select(llvm::ArrayRef<unsigned>,
                                     bool anchor = false,
                                     bool specification = false) const;
};
/// Observe already instantiated layout/placement schemas. This performs no
/// source checking, constructor authorization, or nominal placement
/// recomputation.
llvm::Expected<ProtocolPortLayout> observeProtocolPort(
    std::shared_ptr<const Layout>, const std::optional<ValuePlacement> &,
    uint64_t &remaining, const Limits & = {},
    std::optional<uint64_t> maximumRows = {}, bool checkBounds = true);
/// Contextual single-value carrier. Products use one alternative whose payload
/// is exactly flat->leaves in order, including the empty payload for unit.
/// This representation conveys no source constructor or field-access authority.
struct PackedLayout {
  std::shared_ptr<const Layout> flat;
  protocol::BoundType carrier;
  bool product = false;
  std::string alternative;
};
/// A phase-local cache borrowing an immutable checked project or closed Entry.
/// Keep the owner alive. Work accounting and cache state do not move or copy.
class Layouts {
public:
  explicit Layouts(const CheckedProject &, const Limits & = {});
  explicit Layouts(const ClosedEntry &, const Limits & = {});
  /// All layout and nested semantic work debits the enclosing allowance,
  /// including work performed before a failed observation. The allowance must
  /// outlive this observer.
  Layouts(const ClosedEntry &, const Limits &, uint64_t &remaining);
  ~Layouts();
  Layouts(const Layouts &) = delete;
  Layouts &operator=(const Layouts &) = delete;
  llvm::Expected<std::shared_ptr<const Layout>> get(const Type &);
  llvm::Expected<PackedLayout> packed(const Type &);
  llvm::Expected<ProtocolPortLayout> protocolPort(const Port &);
  /// Body values carry handles directly and need no external row admission.
  llvm::Expected<ProtocolPortLayout> protocolValue(const Value &);
  /// Rebuild exact placed identity from specialized types and checked schemas.
  /// Does not flatten storage or grant source access to private fields.
  llvm::Expected<ValuePlacement> placement(const Type &, const ValuePlacement &,
                                           unsigned participants);
  /// Resolve a closed kind through the shared Contracts owner and the exact row
  /// layout.
  llvm::Expected<OracleKindLayout> oracleKind(const Type &);
  llvm::Expected<std::vector<std::string>>
      kernelArguments(llvm::StringRef, llvm::ArrayRef<Type>);
  /// Select a checked logical product component in the flattened signature.
  /// This computes representation only, not source field-access authority.
  llvm::Expected<LayoutSlice> select(const Declaration &,
                                     const SpecificationSelector &);
  llvm::Expected<LayoutSlice> selectInput(const Declaration &,
                                          const InputSelector &);

private:
  friend class detail::Semantics;
  /// A nested observer of a semantic view inherits that view's authorities.
  Layouts(const std::vector<Declaration> &, const Limits &,
          detail::AuthorityView);
  llvm::ArrayRef<Declaration> definitions;
  Limits limits;
  struct State;
  std::unique_ptr<State> state;
  /// Both memos are confined to this observer, which borrows one immutable
  /// checked project or closed Entry. `cache` is keyed by the lookup key;
  /// `slots` maps each custody slot to the canonical key it digests.
  std::map<std::string, std::string> slots;
  std::map<std::string, std::shared_ptr<const Layout>> cache;
  llvm::Error charge(uint64_t);
  llvm::Error initializeTypes();
  llvm::Expected<ProtocolPortLayout> protocolPort(const Port &,
                                                  bool checkBounds);
  llvm::Expected<LayoutSlice> select(llvm::ArrayRef<Port>, unsigned,
                                     llvm::ArrayRef<unsigned>);
  llvm::Expected<std::shared_ptr<const Layout>> build(const Type &, unsigned);
  llvm::Expected<PackedLayout> pack(std::shared_ptr<const Layout>);
  llvm::Expected<Type>
  substitute(const Type &, const std::map<std::string, Type> &, unsigned);
};
} // namespace zkc::language
#endif
