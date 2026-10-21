#ifndef ZKC_COMPILER_HOST_H
#define ZKC_COMPILER_HOST_H
#include "zkc/Compiler/Language.h"
namespace zkc::language {
/// Immutable exact Host executable bytes; compilation checks source/SSA and
/// independently validates signatures and the complete reached closure.
llvm::Expected<CompiledHost> compileHost(const CheckedOriginal &,
                                         const EntryOptions &);
/// Source-independent carrier admission; publication additionally compares the
/// actual functions and numerical programs with the source-checked original.
llvm::Error checkHostArtifact(llvm::StringRef, const LanguageInterface &,
                              const Limits & = {});
} // namespace zkc::language
#endif
