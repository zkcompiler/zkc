#ifndef ZKC_COMPILER_LANGUAGEDIAGNOSTICS_H
#define ZKC_COMPILER_LANGUAGEDIAGNOSTICS_H
#include "zkc/Compiler/Language.h"
namespace zkc::language {
/// Internal original coordinates used by admission and every machine target.
inline constexpr llvm::StringLiteral originalSourceFilename =
    "zkc-language-original.mlir";
llvm::Error locateCompilationFailure(const CheckedOriginal &, llvm::Error);
} // namespace zkc::language
#endif
