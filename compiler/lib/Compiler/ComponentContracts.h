#ifndef ZKC_COMPILER_COMPONENTCONTRACTS_H
#define ZKC_COMPILER_COMPONENTCONTRACTS_H
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"
namespace zkc::protocol {
struct SourceView;
}
namespace zkc::language {
/// Derive occurrence-local proposals and routes from the admitted original
/// MLIR and its native closed-region view. These attachments carry no
/// mathematical or security evidence.
llvm::Expected<llvm::json::Object>
deriveComponentContracts(const protocol::SourceView &source);
llvm::Error checkComponentContracts(const protocol::SourceView &source,
                                    const llvm::json::Object &actual);
llvm::Error checkComponentDeclarations(const llvm::json::Value &declarations);
} // namespace zkc::language
#endif
