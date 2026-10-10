#ifndef ZKC_LANGUAGE_BINDINGWITNESS_H
#define ZKC_LANGUAGE_BINDINGWITNESS_H
#include "Internal.h"
#include "Semantics.h"
namespace zkc::language::detail {
/// Recover the occurrence's complete shape from its immutable lexical syntax.
/// The caller supplies the body or module environment, never a solver result.
bool checkNotationOccurrence(Semantics &, const Expression &,
                             const NotationEnvironment &);
/// The scope owner re-enumerates expected independently of the inference
/// result. This checker matches ground operands structurally; it does not use
/// the inference search, mutable unification state, or its candidate list.
bool checkOperatorWitness(Semantics &, llvm::ArrayRef<Declaration>,
                          llvm::ArrayRef<OperatorBinding> expected,
                          const NotationDescriptor &, const CallBinding &,
                          llvm::ArrayRef<Type> inputs, const Type &output,
                          Span);
bool checkOperatorOperands(Semantics &, const NotationDescriptor &,
                           const CallBinding &,
                           llvm::ArrayRef<unsigned> parameterOrder,
                           llvm::ArrayRef<ValueId> authoredOperands, Span);
bool checkCallInputMapping(Semantics &, llvm::ArrayRef<unsigned>,
                           unsigned inputs, Span);
bool checkCallAction(Semantics &, llvm::ArrayRef<Declaration>, const Body &,
                     const Operation &);
} // namespace zkc::language::detail
#endif
