#ifndef ZKC_MATHEMATICAL_SUBJECT_H
#define ZKC_MATHEMATICAL_SUBJECT_H

#include "zkc/Mathematical/Registry.h"

namespace zkc::mathematical {

struct Port {
  std::vector<uint32_t> roles;
  TypeId type;
};
struct Permission {
  CapabilitySignature signature;
  std::vector<uint32_t> roles;
};

/// Stable binding position within one region or ordered body. Parameters come
/// first, followed by each result block in declaration order. Nested scopes
/// have their own IDs; captures explicitly connect them to their parent.
struct BindingId {
  uint32_t ordinal;
  bool operator==(BindingId other) const { return ordinal == other.ordinal; }
  bool operator!=(BindingId other) const { return !(*this == other); }
};

/// A checked operand selects a typed lexical binding. The index remains local
/// to this body's context; its complete type/availability is stored explicitly.
struct Operand {
  uint32_t index;
  Port port;
  BindingId binding;
};
struct TypedRegion;
struct TypedNode {
  enum class Kind { Operation, Tuple, Project, Map, Fold };
  Kind kind;
  std::vector<Operand> inputs;
  std::vector<Port> outputs;
  std::vector<NormalStatic> statics;
  std::optional<uint32_t> operation;
  std::optional<uint64_t> component;
  llvm::json::Value attributes = nullptr;
  std::shared_ptr<const TypedRegion> body;
  std::vector<BindingId> outputBindings;
};
struct TypedRegion {
  std::vector<Operand> captures;
  std::vector<Port> parameters;
  std::vector<TypedNode> nodes;
  std::vector<Operand> outputs;
  std::vector<BindingId> parameterBindings;
};
struct TypedBody;
struct TypedStep {
  enum class Kind { Pure, Local, Query, Guard, Message, Invoke, Repeat };
  Kind kind;
  std::optional<uint64_t> site;
  std::vector<Operand> inputs;
  std::vector<Port> outputs;
  std::vector<NormalStatic> statics;
  /// Interpretation-specific declaration reference (operation/wire/callee).
  std::optional<uint32_t> declaration;
  std::vector<uint32_t> roles, capabilities;
  llvm::json::Value attributes = nullptr;
  std::vector<Operand> captures;
  std::shared_ptr<const TypedRegion> region;
  std::shared_ptr<const TypedBody> body;
  std::vector<BindingId> outputBindings;
};
struct TypedReturn {
  std::vector<Operand> values;
};
struct TypedStop {
  uint64_t site;
  uint32_t owner;
  raw::StopReason reason;
};
struct TypedBody {
  std::vector<Port> parameters, results;
  std::vector<TypedStep> steps;
  std::variant<TypedReturn, TypedStop> terminal;
  std::vector<BindingId> parameterBindings;
};
struct TypedRelationBinding {
  uint32_t relation;
  std::vector<NormalStatic> statics;
  std::vector<Operand> publicInputs, witnessInputs;
};
struct TypedDefinition {
  uint64_t staticArity;
  uint32_t roleArity;
  std::vector<Permission> capabilities;
  std::vector<Port> arguments, results;
  std::vector<TypedRelationBinding> relations;
  TypedBody body;
};
struct ClosedInstance {
  uint32_t definition;
  std::vector<uint64_t> statics;
  std::vector<uint32_t> roles, roots;
  TypedDefinition typed;
  /// Direct calls in site preorder, including those in dormant indexed bodies.
  std::vector<std::pair<uint64_t, uint32_t>> callees;
};

/// Successful bounded admission owns the actual typed bodies and immutable
/// captured source. Source, admitted and placed carriers are different APIs.
/// The type table and every derived index belong to this subject only.
class Subject {
  struct Storage;
  std::shared_ptr<const Storage> storage;
  explicit Subject(std::shared_ptr<const Storage> storage)
      : storage(std::move(storage)) {}
  friend class AdmissionBuilder;

public:
  const raw::Subject &source() const;
  const TypeTable &types() const;
  llvm::ArrayRef<TypedDefinition> definitions() const;
  llvm::ArrayRef<ClosedInstance> instances() const;
  llvm::ArrayRef<Permission> roots() const;
  llvm::StringRef digest() const;
};

llvm::Expected<Subject> admit(const llvm::json::Value &, const Registry &,
                              AdmissionBudget budget = {});
llvm::Expected<Subject> admit(const raw::Subject &, const Registry &,
                              AdmissionBudget budget = {});

} // namespace zkc::mathematical
#endif
