#include "OracleRealizationSelection.h"
#include "OracleAccounting.h"
#include "OracleCommonPlan.h"
#include "OracleNativeCommon.h"
#include "OraclePublication.h"
#include "OracleSchedule.h"
#include "zkc/Support/Refusal.h"
#include <map>
using namespace llvm;
namespace zkc::protocol {
Expected<std::vector<OracleRootSelection>>
resolveOracleRealizationSelection(mlir::ModuleOp prepared,
                                  const OracleRealizationPolicy &policy) {
  OracleNativeWork work;
  auto preflight = OracleNativeSourcePreflight::read(prepared, work);
  if (!preflight)
    return preflight.takeError();
  return resolveOracleRealizationSelectionWithWork(prepared, policy, work,
                                                   *preflight);
}
Expected<std::vector<OracleRootSelection>>
resolveOracleRealizationSelectionWithWork(
    mlir::ModuleOp prepared, const OracleRealizationPolicy &policy,
    OracleNativeWork &work, const OracleNativeSourcePreflight &preflight) {
  return oracleExpectedWithWork(
      work, [&]() -> Expected<std::vector<OracleRootSelection>> {
        if (auto e = checkOracleNativePreflight(prepared, work, &preflight))
          return std::move(e);
        // The wire inventory count has a constant-time closed-format limit.
        // Refuse it before reserving or scanning individual root fields.
        if (!work.charge())
          return error("oracle-common-limit");
        if (auto *exact =
                std::get_if<std::vector<OracleRootSelection>>(&policy.roots))
          if (exact->size() > 100000)
            return error("oracle-realization-selection-limit");
        if (!reserveOraclePolicy(policy, work))
          return error("oracle-common-limit");
        auto request = encodeOracleRealizationPolicy(policy);
        if (!request)
          return request.takeError();
        using Key = std::pair<std::string, std::vector<unsigned>>;
        std::map<Key, OracleTableRealization> selected;
        auto *exact =
            std::get_if<std::vector<OracleRootSelection>>(&policy.roots);
        if (exact)
          for (const auto &root : *exact)
            selected.emplace(Key{root.entry, root.path}, root.realization);
        auto entries = oracleEntries(prepared, &work, &preflight);
        if (!entries)
          return entries.takeError();
        if (policy.order == OracleQueryOrder::AfterFinalDraw)
          if (auto e = checkOracleFinalDrawScheduleWithWork(prepared, work,
                                                            preflight))
            return std::move(e);
        std::vector<OracleRootSelection> result;
        for (const auto &entry : *entries) {
          auto storage = planOracleAnchorStorageWithWork(
              prepared, entry,
              [](const auto &) -> Expected<std::string> {
                return std::string();
              },
              work, preflight);
          if (!storage)
            return storage.takeError();
          for (const auto &constructor : storage->constructors) {
            if (constructor.constructor ==
                OracleAnchorConstructor::Kind::Virtual)
              continue;
            if (!work.charge(1 + entry.size() + constructor.path.size()))
              return error("oracle-common-limit");
            OracleTableRealization choice;
            if (auto *uniform =
                    std::get_if<OracleTableRealization>(&policy.roots))
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
      });
}
} // namespace zkc::protocol
