#ifndef ZKC_LANGUAGE_RECORDINTRINSICS_H
#define ZKC_LANGUAGE_RECORDINTRINSICS_H
#include "Semantics.h"
#include "zkc/Language/DeclarationIndex.h"
namespace zkc::language::detail {
bool isRecordIntrinsic(protocol::FrontendSignature);
/// A declaration associated with a record rule.
bool isRecordIntrinsic(const protocol::FrontendDeclaration *);
bool checkDeclarationAssociations(Semantics &, llvm::ArrayRef<Declaration>,
                                  const DeclarationIndex &);
std::optional<Type> recordPayload(Semantics &, const Declaration &,
                                  const Type &, protocol::FrontendSignature,
                                  Span);
bool checkRecordInvocation(Semantics &, llvm::ArrayRef<Declaration>,
                           const DeclarationIndex &, const Body &,
                           const Operation &);
} // namespace zkc::language::detail
#endif
