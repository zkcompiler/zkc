#ifndef ZKC_CONTRACTS_RELATION_H
#define ZKC_CONTRACTS_RELATION_H
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
namespace zkc::relation {
inline std::string formulaSymbol(llvm::StringRef key) {
  std::string material = "zkc.language.predicate:" + key.str();
  return "zkf_" +
         llvm::toHex(llvm::SHA256::hash(llvm::arrayRefFromStringRef(material)),
                     true);
}
} // namespace zkc::relation
#endif
