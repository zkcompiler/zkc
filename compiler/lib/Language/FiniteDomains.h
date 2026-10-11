#ifndef ZKC_LANGUAGE_FINITEDOMAINS_H
#define ZKC_LANGUAGE_FINITEDOMAINS_H
#include "Semantics.h"
namespace zkc::language::detail {
/// Retain a typed factory selection in an enclosing static environment.
/// Data operands have already been evaluated in source order by the caller.
/// Complete recipe expansion belongs to joint domain/callback specialization.
std::optional<unsigned>
instantiateDomain(Semantics &, const Declaration &, const CallableReference &,
                  llvm::ArrayRef<Type>, llvm::ArrayRef<ValueId>,
                  llvm::ArrayRef<unsigned>, llvm::ArrayRef<unsigned>,
                  std::vector<DomainBinding> &,
                  std::vector<DomainApplication> &, Span);
struct DomainOperands {
  std::vector<ValueId> values;
  bool parameterized = false;
};
std::optional<DomainOperands> domainOperands(Semantics &, const Body &,
                                             llvm::ArrayRef<unsigned>, Span);
} // namespace zkc::language::detail
#endif
