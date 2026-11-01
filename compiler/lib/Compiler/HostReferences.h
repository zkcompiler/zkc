#ifndef ZKC_COMPILER_HOSTREFERENCES_H
#define ZKC_COMPILER_HOSTREFERENCES_H
#include "llvm/Support/JSON.h"
#include <map>
namespace zkc::language {
llvm::Error references(
    const llvm::json::Value &,
    std::map<std::string, std::pair<llvm::json::Array, llvm::json::Array>> &,
    llvm::StringRef kind = "invoke");
}
#endif
