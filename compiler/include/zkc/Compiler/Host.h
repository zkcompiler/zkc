#ifndef ZKC_COMPILER_HOST_H
#define ZKC_COMPILER_HOST_H
#include "zkc/Compiler/Language.h"
namespace zkc::language {
/// Check operation semantics and references of functions reconstructed from
/// original SSA, before native boundaries have executable installations.
llvm::Error checkHostFunctions(const llvm::json::Array &,
                               const LanguageInterface &, mlir::ModuleOp,
                               const Limits & = {});
/// Source-independent carrier admission; publication additionally compares the
/// actual functions and numerical programs with the source-checked original.
llvm::Error checkHostArtifact(llvm::StringRef, const LanguageInterface &,
                              const Limits & = {});
} // namespace zkc::language
#endif
