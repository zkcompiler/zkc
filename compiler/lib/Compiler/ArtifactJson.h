#ifndef ZKC_LIB_COMPILER_ARTIFACT_JSON_H
#define ZKC_LIB_COMPILER_ARTIFACT_JSON_H
#include "llvm/Support/JSON.h"
namespace zkc::detail {
/// Bounded object carriers: exact unsigned integer spellings, Unicode scalars,
/// and unique decoded keys. The embedded program has its own array decoder.
llvm::Expected<llvm::json::Value> parseArtifactJson(llvm::StringRef bytes);
} // namespace zkc::detail
#endif
