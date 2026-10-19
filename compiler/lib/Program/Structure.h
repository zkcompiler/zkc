#ifndef ZKC_PROGRAM_INTERNAL_STRUCTURE_H
#define ZKC_PROGRAM_INTERNAL_STRUCTURE_H

#include "zkc/Program/Model.h"
#include "llvm/Support/Error.h"

namespace zkc::program::detail {
/// Bounded reconstruction of native IR before physical selection. This is not
/// interchange admission: these models cannot necessarily be serialized.
llvm::Error checkNativeIRStructure(const LocalDefinitions &);
/// The internal opt-in permits realization applications in logical IR only.
/// Semantic admission still checks their local scope and explicit signatures.
llvm::Error checkNativeIRStructure(const Participants &,
                                   bool allowLogicalRealizations = false);
} // namespace zkc::program::detail
#endif
