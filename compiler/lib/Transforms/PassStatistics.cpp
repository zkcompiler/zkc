#include "zkc/Transforms/PassStatistics.h"
#include "mlir/Pass/Pass.h"
namespace zkc {
struct PassStatistic::Storage {
  mlir::Pass::Statistic value;
  Storage(mlir::Pass *owner, const char *name, const char *description)
      : value(owner, name, description) {}
};
PassStatistic::PassStatistic(mlir::Pass *owner, const char *name,
                             const char *description)
    : storage(std::make_unique<Storage>(owner, name, description)) {}
PassStatistic::~PassStatistic() = default;
void PassStatistic::add(uint64_t value) { storage->value += value; }
bool passStatisticsEnabled() { return LLVM_ENABLE_STATS; }
llvm::json::Array readPassStatistics(mlir::Pass &pass) {
  llvm::json::Array result;
#if LLVM_ENABLE_STATS
  for (auto *stat : pass.getStatistics().take_front(128))
    result.push_back(llvm::json::Object{{"name", std::string(stat->getName())},
                                        {"value", stat->getValue()}});
#else
  (void)pass;
#endif
  return result;
}
} // namespace zkc
