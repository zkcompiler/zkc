#ifndef ZKC_LANGUAGE_MANAGEDSERVICES_H
#define ZKC_LANGUAGE_MANAGEDSERVICES_H
#include "Semantics.h"
#include "zkc/Language/DeclarationIndex.h"
namespace zkc::language::detail {
unsigned serviceStaticCount(protocol::ServiceSignature);
Type serviceResult(protocol::ServiceSignature, const Type &field);
std::optional<CallableReference>
resolveServiceMethod(Semantics &, const DeclarationIndex &, DeclarationId owner,
                     const ResolvedReference &constructor, llvm::StringRef,
                     Span);
bool checkServiceInvocation(Semantics &, llvm::ArrayRef<Declaration>,
                            const DeclarationIndex &, const Body &,
                            const Operation &);
} // namespace zkc::language::detail
#endif
