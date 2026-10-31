#include "NativeProofOrigins.h"
#include "../Transforms/RealizedProtocol.h"
#include "mlir/IR/SymbolTable.h"
#include "zkc/Analysis/Interactions.h"
#include "zkc/Contracts/NativeOrigin.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/SHA256.h"
#include <limits>
#include <map>

using namespace llvm;
using namespace mlir;
namespace zkc::detail {
namespace {
namespace pir = protocol_ir;
using Path = std::vector<unsigned>;
using Steps = std::vector<std::array<std::string, 3>>;
Expected<Path> readPath(const json::Value &value) {
  const auto *array = value.getAsArray();
  if (!array || array->empty() || array->size() > 64)
    return error("native-proof-realization-origin");
  Path path;
  for (const auto &step : *array) {
    auto ordinal = step.getAsUINT64();
    if (!ordinal || *ordinal > std::numeric_limits<unsigned>::max())
      return error("native-proof-realization-origin");
    path.push_back(*ordinal);
  }
  return path;
}
json::Array sourceOrigin(const NativeSourceOrigin &origin) {
  json::Array steps, event;
  for (const auto &step : origin.steps)
    steps.push_back(json::Array{step[0], step[1], step[2]});
  for (const auto &part : origin.event)
    event.push_back(part);
  return json::Array{std::move(steps), std::move(event)};
}
pir::MathematicalOp program(ModuleOp module, StringRef entry) {
  if (!module || !hasSingleElement(module.getBody()->getOperations()))
    return {};
  auto unit = dyn_cast<pir::ProtocolModuleOp>(module.getBody()->front());
  return unit ? dyn_cast_or_null<pir::MathematicalOp>(
                    SymbolTable::lookupSymbolIn(unit, entry))
              : pir::MathematicalOp();
}
} // namespace
Expected<StringMap<NativeSourceOrigin>>
realizedNativeOrigins(const mathematical::RealizedProtocol &realization,
                      StringRef entry,
                      const StringMap<NativeSourceOrigin> &authored) {
  auto original = realization.originalSnapshot();
  auto candidate = realization.candidateSnapshot();
  auto before = program(original.get(), entry);
  auto after = program(candidate.get(), entry);
  if (!before || !after)
    return error("native-proof-realization-origin");
  // The owner already validated this bounded record against the complete
  // actual body. Parsing here does not accept caller-supplied evidence.
  auto record = json::parse(realization.realizationRecord());
  if (!record)
    return record.takeError();
  const auto *root = record->getAsObject();
  const auto *entries = root ? root->getArray("entries") : nullptr;
  if (!entries)
    return error("native-proof-realization-origin");
  const json::Object *selected = nullptr;
  for (const auto &item : *entries) {
    auto *object = item.getAsObject();
    if (!object)
      return error("native-proof-realization-origin");
    if (object->getString("entry") == entry) {
      if (selected)
        return error("native-proof-realization-origin");
      selected = object;
    }
  }
  StringMap<const json::Object *> occurrences;
  std::map<Path, const json::Object *> queryBlocks;
  if (selected) {
    auto *items = selected->getArray("occurrences");
    auto *blocks = selected->getArray("query_blocks");
    if (!items || !blocks)
      return error("native-proof-realization-origin");
    for (const auto &item : *items) {
      auto *object = item.getAsObject();
      auto site = object ? object->getString("site") : std::nullopt;
      if (!site || !occurrences.try_emplace(*site, object).second)
        return error("native-proof-realization-origin");
    }
    for (const auto &item : *blocks) {
      auto *object = item.getAsObject();
      auto *queries = object ? object->getArray("queries") : nullptr;
      if (!queries || queries->empty())
        return error("native-proof-realization-origin");
      auto first = readPath(queries->front());
      if (!first)
        return first.takeError();
      if (!queryBlocks.emplace(*first, object).second)
        return error("native-proof-realization-origin");
    }
  }
  uint64_t remaining = 100000;
  facts::Work work(remaining);
  InteractionAnalysis interactions(original.get());
  const InteractionDeclaration *sourceView = nullptr;
  auto sourceOperation = [&](const Path &path) -> Expected<Operation *> {
    // Ordinary authored events need no oracle association. Do not extract
    // their complete computation merely to rediscover an unused path index.
    if (!sourceView) {
      auto view = interactions.get(before, work);
      if (!view) {
        consumeError(view.takeError());
        return error(work.exhausted() ? "native-proof-origin-limit"
                                      : "native-proof-realization-origin");
      }
      sourceView = *view;
    }
    auto action = sourceView->lookup(path, work);
    if (!action) {
      consumeError(action.takeError());
      return error("native-proof-origin-limit");
    }
    if (!*action)
      return error("native-proof-realization-origin");
    return (*action)->getOperation();
  };
  auto association = [&](const Path &path,
                         Operation *sourceOp) -> Expected<json::Value> {
    json::Array coordinates;
    for (unsigned step : path)
      coordinates.push_back(std::to_string(step));
    json::Value lineage(nullptr);
    if (auto site = sourceOp->getAttrOfType<StringAttr>("site")) {
      auto origin = authored.find(site.getValue());
      if (origin != authored.end())
        lineage = sourceOrigin(origin->second);
      else if (isa<pir::OracleSendOp, pir::OracleQueryOp>(sourceOp))
        return error("native-proof-realization-origin");
    }
    return json::Value(json::Array{entry, std::move(coordinates),
                                   sourceOp->getName().getStringRef(),
                                   std::move(lineage)});
  };
  StringMap<NativeSourceOrigin> result;
  llvm::StringSet<> encodedOrigins;
  auto collect = [&](auto &&self, Block &body,
                     const Steps &repeatFrames) -> Error {
    if (repeatFrames.size() > 64)
      return error("native-proof-origin-limit");
    for (Operation &op : body) {
      if (!work.charge())
        return error("native-proof-origin-limit");
      if (!isa<pir::RepeatOp, pir::ExchangeOp, pir::QueryOp,
               pir::ConstructionStartOp>(op))
        continue;
      auto site = op.getAttrOfType<StringAttr>("site");
      if (!site)
        return error("native-proof-realization-origin");
      NativeSourceOrigin origin;
      auto authoredOrigin = authored.find(site.getValue());
      if (authoredOrigin != authored.end()) {
        origin = authoredOrigin->second;
        if (origin.event.empty() || origin.event[0] == "oracle")
          return error("native-proof-realization-origin");
      } else {
        const auto *metadata = occurrences.lookup(site.getValue());
        auto purpose = metadata ? metadata->getString("purpose") : std::nullopt;
        auto role = metadata ? metadata->getString("role") : std::nullopt;
        auto *coordinate = metadata ? metadata->get("path") : nullptr;
        if (!purpose || !role || !coordinate)
          return error("native-proof-realization-origin");
        auto path = readPath(*coordinate);
        if (!path)
          return path.takeError();
        auto sourceOp = sourceOperation(*path);
        if (!sourceOp)
          return sourceOp.takeError();
        auto source = association(*path, *sourceOp);
        if (!source)
          return source.takeError();
        json::Array queries;
        json::Value capacity(nullptr);
        if (auto block = queryBlocks.find(*path); block != queryBlocks.end()) {
          for (const auto &item : *block->second->getArray("queries")) {
            auto position = readPath(item);
            if (!position)
              return position.takeError();
            auto queryOp = sourceOperation(*position);
            if (!queryOp)
              return queryOp.takeError();
            auto query = association(*position, *queryOp);
            if (!query)
              return query.takeError();
            queries.push_back(std::move(*query));
          }
          capacity = *block->second->get("packet_capacity");
        }
        if (auto message = dyn_cast<pir::ExchangeOp>(op)) {
          bool delivery =
              *purpose == "deliver" && isa<pir::OracleSendOp>(*sourceOp);
          bool opening = (*purpose == "opening_request" ||
                          *purpose == "opening_response") &&
                         isa<pir::OracleQueryOp>(*sourceOp) && !queries.empty();
          if ((!delivery && !opening) || *role != message.getReceiver())
            return error("native-proof-realization-origin");
        } else if (!isa<pir::RepeatOp>(op)) {
          return error("native-proof-realization-origin");
        }
        auto provenance = printJson(json::Array{
            "zkc.oracle-native-occurrence/0", entry, *purpose, *role,
            realization.normalizedSelection(), std::move(*source),
            std::move(queries), std::move(capacity)});
        origin.protocol =
            "zkc.oracle." +
            toHex(SHA256::hash(arrayRefFromStringRef(provenance)), true);
        origin.site = site.str();
        // Keep full authored loop prefixes so generated and authored events
        // inside one loop identify the same frame. The reserved namespace
        // states that this event's site is already expanded; its apply frames
        // remain provenance, not a second spelling expansion.
        origin.steps = repeatFrames;
        bool generatedParent = any_of(repeatFrames, [](const auto &step) {
          return step[0] == "repeat" &&
                 StringRef(step[1]).starts_with("zkc.oracle.");
        });
        if (!generatedParent)
          if (auto sourceSite =
                  (*sourceOp)->getAttrOfType<StringAttr>("site")) {
            auto sourceOrigin = authored.find(sourceSite.getValue());
            if (sourceOrigin != authored.end())
              origin.steps = sourceOrigin->second.steps;
          }
        if (auto message = dyn_cast<pir::ExchangeOp>(op))
          origin.event = {"message",
                          origin.protocol,
                          origin.site,
                          origin.site,
                          message.getSender().str(),
                          message.getReceiver().str()};
        else
          origin.event = {"repeat", origin.protocol, origin.site};
      }
      if (result.size() >= 2048 ||
          !result.try_emplace(site.getValue(), origin).second)
        return error("native-proof-origin-limit");
      if (auto repeat = dyn_cast<pir::RepeatOp>(op)) {
        Steps child(origin.steps);
        child.push_back({"repeat", origin.protocol, origin.site});
        if (auto e = self(self, repeat.getBody().front(), child))
          return e;
      } else {
        auto encoded = protocol::encodeNativeOriginTemplate(entry, origin.steps,
                                                            origin.event);
        if (!encoded)
          return encoded.takeError();
        if (!encodedOrigins.insert(*encoded).second)
          return error("native-proof-realization-origin");
      }
    }
    return Error::success();
  };
  if (auto e = collect(collect, after.getBody().front(), {}))
    return std::move(e);
  for (const auto &item : authored)
    if (!item.second.event.empty() && item.second.event[0] != "oracle" &&
        !result.contains(item.first()))
      return error("native-proof-origin-coverage");
  return result;
}
} // namespace zkc::detail
