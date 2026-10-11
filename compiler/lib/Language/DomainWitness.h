#ifndef ZKC_LANGUAGE_DOMAINWITNESS_H
#define ZKC_LANGUAGE_DOMAINWITNESS_H
#include "DomainClosure.h"
namespace zkc::language::detail {
/// Check a supplied shape and bind its input ports to source operand identities
/// in the caller's SSA space. The shape is compared, never regenerated. The map
/// makes specialization aliases explicit without copying or rewriting a Body.
std::optional<std::vector<ValueId>>
bindDomainInputs(Semantics &, llvm::ArrayRef<Declaration>, const Body &source,
                 const Body &caller, const std::function<ValueId(ValueId)> &,
                 unsigned root, const Substitution &,
                 llvm::ArrayRef<DomainEnvironment>, const DomainShape &,
                 ValueOrigins *cache = nullptr);
/// Relate a supplied descriptor to the checked source recipe, including all
/// admitted factory intermediates. Does not call the closure producer or trust
/// its shape key. Environment operands use the caller body's SSA space.
bool checkDomainClosure(Semantics &, llvm::ArrayRef<Declaration>, const Body &,
                        unsigned root, const Substitution &,
                        llvm::ArrayRef<DomainEnvironment>,
                        const DomainEnvironment &candidate,
                        ValueOrigins *cache = nullptr);
} // namespace zkc::language::detail
#endif
