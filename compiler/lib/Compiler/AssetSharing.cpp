#include "zkc/Compiler/AssetSharing.h"
#include "zkc/Contracts/RingSharing.h"
#include "zkc/Relation/Bundle.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"

using namespace llvm;
namespace zkc::language {
namespace {
Expected<relation::Bundle>
withArenas(const relation::Bundle &original,
           ArrayRef<relation::BundleTable> replacements) {
  auto tables = std::vector<relation::BundleTable>(original.tables().begin(),
                                                   original.tables().end());
  for (unsigned i = 0; i < tables.size(); ++i)
    tables[i].arena = replacements[i].arena;
  return relation::Bundle::create(
      {original.publics().begin(), original.publics().end()},
      {original.channels().begin(), original.channels().end()},
      std::move(tables));
}
} // namespace

Error checkAssetSharing(const Asset &original, const Asset &candidate,
                        ArrayRef<std::vector<uint32_t>> maps) {
  if (const auto *arena = original.ring()) {
    if (!candidate.ring() || maps.size() != 1)
      return error("asset-sharing-kind");
    return ring::checkSharing(*arena, *candidate.ring(), maps.front());
  }
  const auto *bundle = original.bundle();
  const auto *target = candidate.bundle();
  if (!bundle || !target)
    return error("asset-sharing-kind");
  if (bundle->tables().size() != target->tables().size() ||
      maps.size() != bundle->tables().size())
    return error("asset-sharing-shape");
  for (unsigned i = 0; i < maps.size(); ++i)
    if (auto failure = ring::checkSharing(bundle->tables()[i].arena,
                                          target->tables()[i].arena, maps[i]))
      return failure;
  // Re-form the original surrounding relation with the candidate arenas.
  // Equality then covers all public slots, channels, table/group names,
  // authority, height, read model, bindings, scopes and interactions.
  auto retained = withArenas(*bundle, target->tables());
  if (!retained)
    return retained.takeError();
  if (printJson(retained->encode()) != printJson(target->encode()))
    return error("asset-sharing-context");
  return Error::success();
}

Expected<SharedAsset> shareAsset(const Asset &original) {
  std::vector<std::vector<uint32_t>> maps;
  std::string format, body;
  bool changed = false;
  if (const auto *arena = original.ring()) {
    auto sharing = ring::shareExpression(*arena);
    if (!sharing)
      return sharing.takeError();
    changed = sharing->changed;
    maps.push_back(std::move(sharing->nodeMap));
    format = "ring-json";
    body = printJson(sharing->expression.encode());
  } else if (const auto *bundle = original.bundle()) {
    std::vector<relation::BundleTable> tables(bundle->tables().begin(),
                                              bundle->tables().end());
    for (auto &table : tables) {
      auto sharing = ring::shareExpression(table.arena);
      if (!sharing)
        return sharing.takeError();
      changed |= sharing->changed;
      maps.push_back(std::move(sharing->nodeMap));
      table.arena = std::move(sharing->expression);
    }
    auto shared = withArenas(*bundle, tables);
    if (!shared)
      return shared.takeError();
    format = "relation-bundle-json";
    body = printJson(shared->encode());
  } else
    return error("asset-sharing-kind");
  auto asset = Asset::read({original.name().str(), format, body, {}});
  if (!asset)
    return asset.takeError();
  if (auto failure = checkAssetSharing(original, *asset, maps))
    return std::move(failure);
  return SharedAsset{std::move(*asset), std::move(maps), changed};
}
} // namespace zkc::language
