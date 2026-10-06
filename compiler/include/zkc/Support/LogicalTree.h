#ifndef ZKC_SUPPORT_LOGICALTREE_H
#define ZKC_SUPPORT_LOGICALTREE_H
#include "llvm/Support/JSON.h"
namespace zkc {
/// Canonical bounded string/array tree bytes shared by construction formats.
/// Syntax validity does not establish correspondence or authority.
llvm::Expected<std::string> encodeLogicalTree(const llvm::json::Value &tree);
} // namespace zkc
#endif
