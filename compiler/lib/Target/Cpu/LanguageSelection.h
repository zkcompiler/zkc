#ifndef ZKC_TARGET_CPU_LANGUAGESELECTION_H
#define ZKC_TARGET_CPU_LANGUAGESELECTION_H
#include "zkc/Compiler/NativeLanguage.h"
namespace zkc::language::detail {
// Pin a native compilation to the source-language selection by its typed
// source identity, policy and entry. Native compilation has already checked
// the artifact bytes against the same source and options; they are not read
// again here.
llvm::Error checkCompiledProof(const CheckedOriginal &,
                               const NativeProofPolicy &selection,
                               const CompiledNativeProof &);
llvm::Error checkCompiledRun(const CheckedOriginal &, llvm::StringRef entry,
                             const CompiledRun &);
} // namespace zkc::language::detail
#endif
