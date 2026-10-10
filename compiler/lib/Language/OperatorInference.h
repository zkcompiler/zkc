#ifndef ZKC_LANGUAGE_OPERATORINFERENCE_H
#define ZKC_LANGUAGE_OPERATORINFERENCE_H

#include "CallableConstraints.h"

namespace zkc::language::detail {
/// The grammar and lexical environment are supplied by the scope owner. This
/// solver sees only distinct callable identities and their written signatures.
class OperatorInference {
public:
  struct Candidate {
    ExpressionTypes::Callable target;
    std::vector<std::optional<Type>> arguments;
    Span binding;
  };
  struct Selection {
    CallableConstraints constraints;
    Span binding;
  };
  OperatorInference(TypeInference &, Semantics &,
                    const std::vector<Declaration> &);
  void add(uint32_t expression, Span, std::vector<TypeInference::Variable>,
           TypeInference::Variable result, std::vector<Candidate>);
  /// Add equations implied by singleton candidate families. This supplies
  /// structural contexts such as match without finalizing any call identity.
  bool propagate(Span);
  /// Resolve all pending occurrences together. No capability/effect/body check
  /// occurs in search. The callback reports whether the surrounding statement's
  /// expression types and named-call statics are solved, without completing
  /// their contracts.
  std::optional<std::map<uint32_t, Selection>>
  solve(Span, const std::function<bool()> &complete);

private:
  struct Choice {
    uint32_t expression;
    Span span;
    std::vector<TypeInference::Variable> inputs;
    TypeInference::Variable result;
    std::vector<Candidate> candidates;
  };
  struct Chosen {
    unsigned candidate;
    CallableConstraints application;
  };
  bool propagate(std::map<unsigned, Chosen> &);
  TypeInference &types;
  Semantics &semantics;
  const std::vector<Declaration> &declarations;
  std::vector<Choice> choices;
  std::optional<CallableConstraints> apply(const Choice &, const Candidate &,
                                           bool *signatureFits = nullptr);
  bool coherence(const Choice &, const Candidate &);
};
} // namespace zkc::language::detail
#endif
