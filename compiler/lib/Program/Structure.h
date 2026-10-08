#ifndef ZKC_PROGRAM_INTERNAL_STRUCTURE_H
#define ZKC_PROGRAM_INTERNAL_STRUCTURE_H

#include "zkc/Program/Model.h"
#include "llvm/Support/Error.h"

namespace zkc::program::detail {
/// Bounded reconstruction of native IR before physical selection. This is not
/// interchange admission: these models cannot necessarily be serialized.
llvm::Error checkNativeIRStructure(const LocalDefinitions &);
llvm::Error checkNativeIRStructure(const Participants &);
} // namespace zkc::program::detail
#endif
