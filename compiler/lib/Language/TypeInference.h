#ifndef ZKC_LANGUAGE_TYPEINFERENCE_H
#define ZKC_LANGUAGE_TYPEINFERENCE_H
#include "Semantics.h"

namespace zkc::language::detail {
/// Private type equations. Declaration parameters remain rigid; only variables
/// allocated by this object can be solved. No inference term enters checked IR.
class TypeInference {
public:
  using Variable = unsigned;
  using Parameters = std::map<std::string, Variable>;
  explicit TypeInference(Semantics &types) : types(types) {}
  Variable fresh(Span);
  Variable known(const Type &, Span);
  Variable shape(Type, std::vector<Variable>, Span);
  Variable instantiate(const Type &, const Parameters &, Span);
  /// Fail at the use site; retain the declaration origin in related notes.
  Variable instantiate(const Type &, const Parameters &, Span use, Span origin);
  bool equal(Variable, Variable, Span);
  bool requireKinds(Variable, std::initializer_list<Type::Kind>, Span);
  bool allows(Variable, Type::Kind);
  std::optional<Type> get(Variable, Span);
  /// Forward computations (associations, projections) may wait for their input
  /// types. They never infer those inputs by inverting the computation.
  void defer(std::function<bool()>);
  bool solve(Span);

private:
  struct Node {
    unsigned parent, rank = 0;
    Span origin;
    std::optional<Type> head;
    std::vector<Variable> arguments;
    uint32_t kinds = ~uint32_t(0);
  };
  Semantics &types;
  std::vector<Node> nodes;
  std::vector<std::function<bool()>> pending;
  uint64_t revision = 0;
  Variable root(Variable);
  bool occurs(Variable, Variable, Span, unsigned = 1);
  bool equal(Variable, Variable, Span, unsigned);
  std::optional<Type> get(Variable, Span, unsigned);
  Variable instantiate(const Type &, const Parameters &, Span, Span, unsigned);
};

/// Solved source facts, shared by expression checking and its nested regions.
/// Values, effects, resource use and participant choices are deliberately
/// absent.
struct ExpressionTypes {
  struct Callable {
    DeclarationId declaration;
    std::optional<Type> component;
  };
  std::set<uint32_t> covered;
  std::map<uint32_t, Type> expressions;
  std::map<uint32_t, std::vector<Type>> arguments;
  /// Authored argument index -> declared input index; operands are evaluated
  /// in authored order and only their resulting values are canonicalized.
  std::map<uint32_t, std::vector<unsigned>> inputs;
  /// Resolve against the authored declaration once; body checking consumes the
  /// same target, including bound interface members and nominal constructors.
  std::map<uint32_t, Callable> callees;
};
} // namespace zkc::language::detail
#endif
