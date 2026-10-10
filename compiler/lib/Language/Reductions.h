#ifndef ZKC_LANGUAGE_REDUCTIONS_H
#define ZKC_LANGUAGE_REDUCTIONS_H
#include "Internal.h"
#include "TypeInference.h"
namespace zkc::language::detail {
struct ReductionSource {
  DeclarationId owner, helper;
  uint32_t expression;
  std::shared_ptr<const SyntaxDeclaration> syntax;
  ExpressionTypes inference;
  std::map<BindingId, ValueId> environment;
  std::vector<ValueId> collections;
};
bool reductionTarget(Semantics &, const Declaration &,
                     const CallableReference &, llvm::ArrayRef<Type>, Span);
bool checkReductionRing(Semantics &, llvm::ArrayRef<Declaration>, const Body &,
                        const Type &, Span);
llvm::Error checkReductions(const CheckedStorage &, Work &);
} // namespace zkc::language::detail
#endif
