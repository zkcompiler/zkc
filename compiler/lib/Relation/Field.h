#ifndef ZKC_RELATION_FIELD_H
#define ZKC_RELATION_FIELD_H

#include "zkc/Protocol/Domains.h"
#include "zkc/Protocol/Kernels.h"
#include "zkc/Target/Json.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallString.h"

namespace zkc::relation {
/// Host-side interpretation and normalization, not a cryptographic backend.
class Field {
public:
  /// This APInt evaluator implements prime fields only. An extension can have
  /// the same natural-cast characteristic without sharing this representation.
  static llvm::StringRef primeModulus(llvm::StringRef identity) {
    if (!protocol::installedDomains().hasFact("PrimeField", {identity.str()}))
      return {};
    return protocol::fieldModulus(identity);
  }
  explicit Field(llvm::StringRef modulus)
      : width(2 * llvm::APInt::getBitsNeeded(modulus, 10) + 1),
        modulus(width, modulus, 10) {}

  llvm::Expected<llvm::APInt> parse(llvm::StringRef text) const {
    if (text.empty() || text.size() > 256 ||
        (text.size() != 1 && text.front() == '0') ||
        !llvm::all_of(text, [](char c) { return c >= '0' && c <= '9'; }) ||
        llvm::APInt::getBitsNeeded(text, 10) > width)
      return zkc::error("relation-coefficient");
    llvm::APInt value(width, text, 10);
    if (value.uge(modulus))
      return zkc::error("relation-coefficient");
    return value;
  }
  llvm::APInt zero() const { return llvm::APInt(width, 0); }
  llvm::APInt one() const { return llvm::APInt(width, 1); }
  llvm::APInt add(const llvm::APInt &a, const llvm::APInt &b) const {
    return (a + b).urem(modulus);
  }
  llvm::APInt mul(const llvm::APInt &a, const llvm::APInt &b) const {
    return (a * b).urem(modulus);
  }
  static std::string print(const llvm::APInt &a) {
    llvm::SmallString<80> text;
    a.toString(text, 10, false);
    return text.str().str();
  }

private:
  unsigned width;
  llvm::APInt modulus;
};
} // namespace zkc::relation
#endif
