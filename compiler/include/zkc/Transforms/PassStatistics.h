#ifndef ZKC_TRANSFORMS_PASS_STATISTICS_H
#define ZKC_TRANSFORMS_PASS_STATISTICS_H
#include "llvm/Support/JSON.h"
#include <cstdint>
#include <memory>
namespace mlir {
class Pass;
}
namespace zkc {
/// Keep LLVM's assertion-dependent statistic layout out of project passes.
/// Construction, updates and observation use the linked MLIR library's ABI.
class PassStatistic {
  struct Storage;
  std::unique_ptr<Storage> storage;

public:
  PassStatistic(mlir::Pass *owner, const char *name, const char *description);
  ~PassStatistic();
  void add(uint64_t value);
};
bool passStatisticsEnabled();
llvm::json::Array readPassStatistics(mlir::Pass &pass);
} // namespace zkc
#endif
