#ifndef ZKC_COMPILER_COMPONENTCONTRACTS_H
#define ZKC_COMPILER_COMPONENTCONTRACTS_H
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"
namespace zkc::language {
/// Derive occurrence-local proposals and routes from the verified original
/// export. These attachments carry no mathematical or security evidence.
llvm::Expected<llvm::json::Object>
deriveComponentContracts(const llvm::json::Value &snapshot);
llvm::Error checkComponentContracts(const llvm::json::Value &snapshot,
                                    const llvm::json::Object &actual);
llvm::Error checkComponentDeclarations(const llvm::json::Value &declarations);
} // namespace zkc::language
#endif
