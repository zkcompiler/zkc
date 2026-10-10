#ifndef ZKC_LANGUAGE_BINDINGWITNESS_H
#define ZKC_LANGUAGE_BINDINGWITNESS_H
#include "Internal.h"
#include "Semantics.h"
namespace zkc::language::detail {
/// The scope owner re-enumerates expected independently of the inference
/// result. This checker matches ground operands structurally; it does not use
/// the inference search, mutable unification state, or its candidate list.
bool checkOperatorWitness(Semantics &, llvm::ArrayRef<Declaration>,
                          llvm::ArrayRef<OperatorBinding> expected,
                          const CallBinding &, llvm::ArrayRef<Type> inputs,
                          const Type &output, Span);
bool checkOperatorOperands(Semantics &, const CallBinding &,
                           llvm::ArrayRef<unsigned> parameterOrder,
                           llvm::ArrayRef<ValueId> authoredOperands, Span);
bool checkCallAction(Semantics &, llvm::ArrayRef<Declaration>, const Body &,
                     const Operation &);
} // namespace zkc::language::detail
#endif
