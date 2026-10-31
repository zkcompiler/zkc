#include "OracleRealizationSelection.h"
#include "OracleCommonPlan.h"
#include "OracleSchedule.h"
#include "zkc/Support/Refusal.h"
#include <map>
using namespace llvm;
namespace zkc::protocol {
Expected<std::vector<OracleRootSelection>>
resolveOracleRealizationSelection(mlir::ModuleOp prepared,
                                  const OracleRealizationPolicy &policy) {
  auto request = encodeOracleRealizationPolicy(policy);
  if (!request)
    return request.takeError();
  using Key = std::pair<std::string, std::vector<unsigned>>;
  std::map<Key, OracleTableRealization> selected;
  auto *exact = std::get_if<std::vector<OracleRootSelection>>(&policy.roots);
  if (exact)
    for (const auto &root : *exact)
      selected.emplace(Key{root.entry, root.path}, root.realization);
  auto entries = oracleEntries(prepared);
  if (!entries)
    return entries.takeError();
  if (policy.order == OracleQueryOrder::AfterFinalDraw)
    if (auto e = checkOracleFinalDrawSchedule(prepared))
      return std::move(e);
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
      if (auto *uniform = std::get_if<OracleTableRealization>(&policy.roots))
        choice = *uniform;
      if (exact) {
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
