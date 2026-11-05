#ifndef ZKC_LANGUAGE_CALLABLECONSTRAINTS_H
#define ZKC_LANGUAGE_CALLABLECONSTRAINTS_H

#include "TypeInference.h"

namespace zkc::language::detail {
/// A signature instance contains equations only. It cannot complete a body,
/// infer a capability, choose an owner, or consume an operand.
struct CallableConstraints {
  ExpressionTypes::Callable target;
  TypeInference::Parameters parameters;
  std::vector<TypeInference::Variable> inputs, outputs;
};

CallableConstraints instantiateCallable(TypeInference &, Semantics &,
                                        const Declaration &,
                                        ExpressionTypes::Callable, Span,
                                        bool includeOutputs = true);
/// Returns an empty optional while a static is unknown. The diagnostic, if
/// any, distinguishes a contradiction from an unresolved forward equation.
std::optional<std::vector<Type>> callableArguments(TypeInference &, Semantics &,
                                                   const Declaration &,
                                                   const CallableConstraints &,
                                                   Span);
} // namespace zkc::language::detail
#endif
