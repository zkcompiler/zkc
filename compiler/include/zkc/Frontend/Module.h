#ifndef ZKC_FRONTEND_MODULE_H
#define ZKC_FRONTEND_MODULE_H

#include "zkc/Source/Model.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <limits>
#include <memory>

namespace zkc::frontend {
namespace model {
struct Module;
}
class Analysis;
/// A successful source check is the only way to obtain this immutable handle.
class CheckedModule {
  std::shared_ptr<const model::Module> model;
  explicit CheckedModule(std::shared_ptr<const model::Module> value)
      : model(std::move(value)) {}
  friend class Analysis;
  friend llvm::Expected<source::Content> lower(const CheckedModule &);
  friend llvm::Expected<source::Construction>
  bindConstruction(const CheckedModule &, source::Construction);
};
/// Ordinals belong to one immutable source module. They are not artifact
/// identities.
template <typename Tag> struct ModelId {
  uint32_t index = std::numeric_limits<uint32_t>::max();
  bool valid() const { return index != std::numeric_limits<uint32_t>::max(); }
  friend bool operator==(ModelId a, ModelId b) { return a.index == b.index; }
  friend bool operator!=(ModelId a, ModelId b) { return !(a == b); }
  friend bool operator<(ModelId a, ModelId b) { return a.index < b.index; }
};
using DeclId = ModelId<struct DeclTag>;
using ValueId = ModelId<struct ValueTag>;
using ScopeId = ModelId<struct ScopeTag>;
using TypeId = ModelId<struct TypeTag>;
using DomainId = ModelId<struct DomainTag>;

struct Domain {
  enum class Kind { Identity, Parameter, Projection };
  Kind kind = Kind::Identity;
  std::string name, sort;
  DeclId parameter;
  DomainId parent;
};
struct Type {
  enum class Kind { Logical, Record, Product, Array };
  Kind kind = Kind::Logical;
  std::string constructor;
  DeclId declaration; // Required for Record; no structural record equivalence.
  std::vector<DomainId> arguments;
  std::vector<TypeId> elements; // Product elements; unit is the empty product.
  // Array has exactly one element type even when count is zero.
  uint64_t count = 0;
};
struct Scope {
  ScopeId id, parent;
  DeclId owner;
};
/// A lexical source binding survives layout into leaf SSA values. Mutability
/// belongs to the source name, not to the values in its lowering layout.
struct LocalBinding {
  ValueId id;
  ScopeId scope;
  TypeId type;
  std::string name;
  source::Names leaves;
  bool mutableBinding = false;
  std::optional<source::Span> location;
};
struct ValueUse {
  ValueId binding;
  ScopeId scope;
  std::optional<source::Span> location;
};
struct Port {
  std::string name, role;
  TypeId type;
  std::optional<source::Span> location;
};
struct Requirement {
  std::string predicate;
  std::vector<DomainId> arguments;
  std::optional<source::Span> location;
};
struct Declaration {
  enum class BodyState { External, Deferred, Checked };
  enum class Kind {
    Function,
    Protocol,
    Record,
    Parameter,
    Binding,
    Configuration,
    Dependency,
    Instance,
    Entry,
    Relation,
    RelationView,
    Bundle,
    Operation,
    Constant
  };
  DeclId id;
  ScopeId scope, members;
  Kind kind = Kind::Function;
  std::string name, sort;
  std::optional<source::Span> location;
  /// Readable source path and exact nominal identity; name remains the symbol
  /// used by the typed model and lowering. Empty for generated/local bindings.
  std::string displayName, identity;
  /// Actual common-source name retained after successful structural lowering;
  /// this does not imply independent PIR admission or execution readiness.
  std::optional<std::string> loweredName;
  bool generic = false, checked = false, hasBody = false;
  /// Formation and source body checking are separate from common admission.
  /// Deferred denotes a body not yet checked (including failed partial states).
  bool signatureChecked = false;
  /// Present only for a successfully evaluated named natural constant.
  std::optional<uint64_t> constantValue;
  BodyState bodyState = BodyState::External;
  source::Names roles, naturalParameters;
  std::vector<DeclId> parameters, constructors;
  std::vector<Port> inputs, outputs, fields;
  std::vector<Requirement> requirements;
  DeclId target; // Resolved configuration/dependency/instance/entry target.
};
struct ParameterBinding {
  DeclId parameter;
  DomainId argument;
};
struct ResolvedUse {
  enum class Kind { Call, Construct, Invoke };
  Kind kind = Kind::Call;
  DeclId owner, target;
  ScopeId scope;
  std::optional<source::Span> location;
  std::string site, role;
  bool writtenArguments = false;
  std::vector<ParameterBinding> bindings;
  std::vector<Port> results;
  std::vector<Requirement> requirements;
};
struct Instantiation {
  DeclId definition, emitted;
  std::optional<source::Span> location;
  std::vector<ParameterBinding> bindings;
};
struct SemanticDependency {
  enum class Kind {
    Interface,
    Body,
    LinkLayout,
    Evidence,
    DiagnosticProvenance
  };
  Kind kind = Kind::Body;
  /// Exact nominal identities or exact checked content keys, not fingerprints.
  std::string source, target;
  std::optional<source::Span> location;
};
} // namespace zkc::frontend
#endif
