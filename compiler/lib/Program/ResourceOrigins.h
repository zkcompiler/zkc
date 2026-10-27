#ifndef ZKC_PROGRAM_INTERNAL_RESOURCE_ORIGINS_H
#define ZKC_PROGRAM_INTERNAL_RESOURCE_ORIGINS_H

#include "zkc/Program/Admission.h"

namespace zkc::program::detail {
// Formation, complete callback bodies and acyclicity have already passed.
// Check every finite state obligation, including unused requests.
llvm::Error verifyFiniteResourceOrigins(
    const LocalDefinitions &definitions,
    llvm::ArrayRef<protocol::LocalRealization> realizations);
} // namespace zkc::program::detail
#endif
