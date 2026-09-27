#ifndef ZKC_FRONTEND_CARRIER_SPELLING_H
#define ZKC_FRONTEND_CARRIER_SPELLING_H

#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Declarations.h"
#include "llvm/ADT/ArrayRef.h"

namespace zkc::frontend::carrier {
inline bool operationContract(llvm::StringRef name) {
  for (const auto &contract : protocol::boundOperationContracts())
    if (contract.name == name)
      return true;
  return false;
}

/// Only installed exports are syntax aliases. Exact quoted strings bypass this
/// inverse spelling map and retain the common checker's binder interpretation.
inline llvm::StringRef typeConstructor(llvm::ArrayRef<std::string> path) {
  if (path.size() == 1 && (path[0] == "bool" || path[0] == "index"))
    return path[0];
  std::string qualified;
  for (const auto &segment : path) {
    if (!qualified.empty())
      qualified += "::";
    qualified += segment;
  }
  llvm::StringRef result;
  for (const auto &entry : protocol::sourceTypeExports()) {
    if ((path.size() == 1 && path[0] == entry.name) ||
        qualified == entry.module + "::" + entry.name) {
      if (!result.empty() && result != entry.constructor)
        return {}; // An unqualified export must be unambiguous.
      result = entry.constructor;
    }
  }
  return result;
}
} // namespace zkc::frontend::carrier

#endif
