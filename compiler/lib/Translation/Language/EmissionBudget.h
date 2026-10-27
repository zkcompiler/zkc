#ifndef ZKC_TRANSLATION_LANGUAGE_EMISSION_BUDGET_H
#define ZKC_TRANSLATION_LANGUAGE_EMISSION_BUDGET_H

#include "mlir/IR/Builders.h"
#include <cstdint>
#include <limits>

namespace zkc::language {
// Count every insertion made through the source constructor's shared builder,
// including packing and CFG construction delegated to another implementation.
// This listener cannot cancel insertion: callers preflight known batches and
// check again at construction boundaries before publishing any module.
// Source construction inserts fresh operations, not prebuilt operation trees.
class EmissionBudget final : public mlir::OpBuilder::Listener {
public:
  explicit EmissionBudget(uint64_t limit) : limit(limit) {}
  bool allows(uint64_t additional = 0) const {
    return !overflow && inserted <= limit && additional <= limit - inserted;
  }
  uint64_t count() const { return inserted; }
  void notifyOperationInserted(mlir::Operation *,
                               mlir::OpBuilder::InsertPoint) override {
    if (inserted == std::numeric_limits<uint64_t>::max())
      overflow = true;
    else
      ++inserted;
  }

private:
  uint64_t limit, inserted = 0;
  bool overflow = false;
};
} // namespace zkc::language
#endif
