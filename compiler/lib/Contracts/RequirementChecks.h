#ifndef ZKC_CONTRACTS_REQUIREMENT_CHECKS_H
#define ZKC_CONTRACTS_REQUIREMENT_CHECKS_H

#include "zkc/Contracts/Requirements.h"

namespace zkc::requirements {
// Formation and resource bounds shared by generic admission and proof
// production.
llvm::Error checkFormation(llvm::ArrayRef<Term>, llvm::ArrayRef<Predicate>,
                           llvm::ArrayRef<Implication>,
                           llvm::ArrayRef<Predicate>);
} // namespace zkc::requirements
#endif
