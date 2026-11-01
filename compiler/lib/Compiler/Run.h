#ifndef ZKC_LIB_COMPILER_RUN_H
#define ZKC_LIB_COMPILER_RUN_H
#include "zkc/Program/Model.h"
#include "llvm/Support/Error.h"
namespace zkc::detail {
/// Decode the current bundle and independently admit its executable program.
/// Source role correspondence and publication checks remain separate.
llvm::Expected<program::Participants> readRunProgram(llvm::StringRef);
} // namespace zkc::detail
#endif
