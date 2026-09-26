#ifndef ZKC_CONTRACTS_RESOURCE_UNIT_H
#define ZKC_CONTRACTS_RESOURCE_UNIT_H
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringRef.h"
namespace zkc::protocol {
// Exact closed slot identity, never a static algebraic domain or evidence.
inline bool resourceUnitDomain(llvm::StringRef domain) {
  auto letter = [](char c) {
    return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z');
  };
  return !domain.empty() && domain.size() <= 128 && letter(domain.front()) &&
         llvm::all_of(domain, [&](char c) {
           return letter(c) || (c >= '0' && c <= '9') || c == '_' || c == '-' ||
                  c == '.';
         });
}
inline bool resourceUnitContract(llvm::StringRef contract) {
  return contract == "resource_unit.create" ||
         contract == "resource_unit.pass" ||
         contract == "resource_unit.consume";
}
} // namespace zkc::protocol
#endif
