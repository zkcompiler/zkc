#ifndef ZKC_SOURCE_INTERNAL_STRUCTURE_H
#define ZKC_SOURCE_INTERNAL_STRUCTURE_H

#include "zkc/Source/Model.h"
#include "llvm/Support/Error.h"

namespace zkc::source::detail {
/// Bounded reconstruction of native IR before physical selection. This is not
/// interchange admission: these models cannot necessarily be serialized.
llvm::Error checkNativeIRStructure(const Module &);
llvm::Error checkNativeIRStructure(const Participants &);
} // namespace zkc::source::detail
#endif
