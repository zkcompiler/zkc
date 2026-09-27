#ifndef ZKC_FRONTEND_RESOLUTION_INSTALLED_H
#define ZKC_FRONTEND_RESOLUTION_INSTALLED_H

#include "zkc/Contracts/Declarations.h"
#include "llvm/ADT/StringRef.h"
#include <string>

namespace zkc::frontend::resolution {
inline std::string installedTypeSymbol(llvm::StringRef constructor) {
  return "__installed_type_" + constructor.str();
}
inline std::string installedOperationSymbol(llvm::StringRef contract) {
  return "__installed_operation_" + contract.str();
}
} // namespace zkc::frontend::resolution
#endif
