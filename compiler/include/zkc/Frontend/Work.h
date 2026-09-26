#ifndef ZKC_FRONTEND_WORK_H
#define ZKC_FRONTEND_WORK_H

#include <array>
#include <cstddef>
#include <cstdint>

namespace zkc::frontend {
/// Logical compiler operations, not time, bytes, or portable admission limits.
enum class WorkAccount {
  AuthoredStatic,
  LibraryFormation,
  GeneratedSource,
  Output
};
struct WorkLimits {
  uint64_t authoredStatic = 262144;
  uint64_t libraryFormation = 262144;
  uint64_t generatedSource = 262144;
  uint64_t output = 262144;
};
using WorkUsage = std::array<uint64_t, 4>;

/// Owned by one invocation. Borrow only during a call; never retain in a
/// checked environment. A failed charge consumes nothing and cannot wrap.
class WorkBudget {
  WorkUsage limits;
  WorkUsage consumed{};

public:
  explicit WorkBudget(WorkLimits limits = {})
      : limits{limits.authoredStatic, limits.libraryFormation,
               limits.generatedSource, limits.output} {}
  bool charge(WorkAccount account, uint64_t amount = 1) {
    auto index = static_cast<size_t>(account);
    if (amount > limits[index] - consumed[index])
      return false;
    consumed[index] += amount;
    return true;
  }
  bool chargeProduct(WorkAccount account, uint64_t count, uint64_t amount) {
    auto index = static_cast<size_t>(account);
    if (count && amount > (limits[index] - consumed[index]) / count)
      return false;
    return charge(account, count * amount);
  }
  uint64_t used(WorkAccount account) const {
    return consumed[static_cast<size_t>(account)];
  }
  const WorkUsage &usage() const { return consumed; }
};
} // namespace zkc::frontend
#endif
