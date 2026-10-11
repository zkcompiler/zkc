#ifndef ZKC_LANGUAGE_DOMAINCLOSURE_H
#define ZKC_LANGUAGE_DOMAINCLOSURE_H
#include "Semantics.h"
namespace zkc::language::detail {
class ValueOrigins;
struct DomainEnvironment {
  std::shared_ptr<const DomainShape> shape;
  /// SSA values in the body where this environment is consumed.
  std::vector<ValueId> operands;
};
/// Close one consumed domain, including every constructor in each selected
/// factory. Unrelated domains in the enclosing Body are not traversed.
std::optional<DomainEnvironment>
closeDomain(Semantics &, llvm::ArrayRef<Declaration>, const Body &, unsigned,
            const Substitution &, llvm::ArrayRef<DomainEnvironment>,
            ValueOrigins *cache = nullptr);
} // namespace zkc::language::detail
#endif
