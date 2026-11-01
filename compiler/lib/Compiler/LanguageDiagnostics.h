#ifndef ZKC_COMPILER_LANGUAGEDIAGNOSTICS_H
#define ZKC_COMPILER_LANGUAGEDIAGNOSTICS_H
#include "zkc/Compiler/Language.h"
namespace zkc::language {
llvm::Error locateCompilationFailure(const CheckedOriginal &, llvm::Error);
}
#endif
