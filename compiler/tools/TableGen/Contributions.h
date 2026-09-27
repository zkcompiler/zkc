#ifndef ZKC_TABLEGEN_CONTRIBUTIONS_H
#define ZKC_TABLEGEN_CONTRIBUTIONS_H

#include "llvm/ADT/StringRef.h"
#include <map>
#include <vector>

namespace llvm {
class Record;
class RecordKeeper;
} // namespace llvm

// Build ownership controls enumeration, not the interpretation of a
// declaration.
class DeclarationOrder {
public:
  explicit DeclarationOrder(const llvm::RecordKeeper &records);
  std::vector<const llvm::Record *> sort(llvm::StringRef category) const;

private:
  const llvm::RecordKeeper &records;
  std::map<const llvm::Record *, unsigned> owners;
  bool composed = false;
};

#endif
