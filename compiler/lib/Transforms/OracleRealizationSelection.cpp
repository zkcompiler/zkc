#include "OracleRealizationSelection.h"
#include "OracleCommonPlan.h"
#include "zkc/Support/Refusal.h"
#include <map>
using namespace llvm;
namespace zkc::protocol {
Expected<std::vector<OracleRootSelection>>
resolveOracleRealizationSelection(mlir::ModuleOp prepared,
                                  const OracleRealizationPolicy &policy) {
  if (policy.flush != OracleQueryFlush::Immediate &&
      policy.flush != OracleQueryFlush::AfterFinalDraw)
    return error("oracle-realization-selection");
  using Key = std::pair<std::string, std::vector<unsigned>>;
  std::map<Key, OracleTableRealization> selected;
  if (policy.roots) {
    if (policy.roots->size() > 100000)
      return error("oracle-realization-selection-limit");
    for (const auto &root : *policy.roots) {
      const auto &choice = root.realization;
      if (root.path.empty() || root.path.size() > 64 ||
          (choice.grouping != OracleLeafGrouping::Individual &&
           choice.grouping != OracleLeafGrouping::AntipodalPairs) ||
          (choice.order != OracleLeafOrder::Natural &&
           choice.order != OracleLeafOrder::BitReversed) ||
          (choice.scheme.empty() &&
           (choice.grouping != OracleLeafGrouping::Individual ||
            choice.order != OracleLeafOrder::Natural)) ||
          !selected.emplace(Key{root.entry, root.path}, choice).second)
        return error("oracle-realization-selection");
    }
  }
  auto entries = oracleEntries(prepared);
  if (!entries)
    return entries.takeError();
  // The path-sensitive observation reader must authorize this policy once
  // common queries are present. Until that integration is available, never
  // label an unchecked query schedule as post-final-draw.
  if (policy.flush == OracleQueryFlush::AfterFinalDraw) {
    bool hasQuery = false;
    prepared.walk([&](protocol_ir::OracleQueryOp) { hasQuery = true; });
    if (hasQuery)
      return error("oracle-realization-flush-profile");
  }
  std::vector<OracleRootSelection> result;
  for (const auto &entry : *entries) {
    auto storage = planOracleAnchorStorage(
        prepared, entry,
        [](const auto &) -> Expected<std::string> { return std::string(); });
    if (!storage)
      return storage.takeError();
    for (const auto &constructor : storage->constructors) {
      if (constructor.constructor == OracleAnchorConstructor::Kind::Virtual)
        continue;
      OracleTableRealization choice;
      if (policy.roots) {
        auto found = selected.find({entry, constructor.path});
        if (found == selected.end())
          return error("oracle-realization-selection");
        choice = found->second;
        selected.erase(found);
      }
      if (result.size() >= 100000)
        return error("oracle-realization-selection-limit");
      result.push_back({entry, constructor.path, std::move(choice)});
    }
  }
  if (!selected.empty())
    return error("oracle-realization-selection");
  return result;
}
} // namespace zkc::protocol
