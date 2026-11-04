#include "zkc/Compiler/SourceCorrespondence.h"
#include "SourceArtifacts.h"
#include "SourceView.h"
#include "mlir/IR/BuiltinAttributes.h"
#include "zkc/Language/InspectionData.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <functional>
#include <map>
#include <set>
#include <tuple>

using namespace llvm;
namespace zkc::language {
namespace detail {
json::Object sourceAdmission(const CheckedOriginal &original) {
  auto sha256 = [](StringRef bytes) {
    return "sha256:" + toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
  };
  return json::Object{
      {"format", "zkc.structured-source/0"},
      {"original_sha256", sha256(original.bytes())},
      {"protocol_symbol", original.entry().protocol().symbol},
      {"interface_sha256", sha256(original.interfaceJson())},
      {"capture", original.entry().project().capture().identity()},
      {"installation", original.entry().project().installationIdentity()}};
}
} // namespace detail
namespace {
using SpanKey = std::tuple<std::string, uint64_t, uint64_t>;
SpanKey key(const json::Object &span) {
  return {span.getString("module")->str(), *span.getInteger("begin"),
          *span.getInteger("end")};
}
StringRef derivation(protocol::StructuredSourceDerivation kind) {
  switch (kind) {
  case protocol::StructuredSourceDerivation::Direct:
    return "direct";
  case protocol::StructuredSourceDerivation::ScopedExecution:
    return "scoped_execution";
  case protocol::StructuredSourceDerivation::Computation:
    return "computation";
  }
  llvm_unreachable("unknown source derivation");
}
class Associations {
  const CheckedOriginal &original;
  const Limits &limits;
  uint64_t remaining;
  using Position = std::pair<unsigned, unsigned>;
  std::map<Position, std::vector<Span>> locations;
  std::map<SpanKey, json::Array> written;
  Error charge(uint64_t amount) {
    if (amount > remaining)
      return error("source.limit", "source association work limit exceeded");
    remaining -= amount;
    return Error::success();
  }
  json::Object span(Span value) const {
    return json::Object{
        {"module",
         original.entry().project().sources()[value.source.index].module},
        {"begin", value.begin},
        {"end", value.end}};
  }

public:
  Associations(const CheckedOriginal &original, const Limits &limits)
      : original(original), limits(limits), remaining(limits.work) {}
  Expected<json::Array>
  run(const json::Value &ast,
      ArrayRef<protocol::StructuredSourceAssociation> rows) {
    for (const auto &location : original.locations()) {
      if (auto e = charge(1))
        return std::move(e);
      // Installed declarations have no captured written source. Their exact
      // original row remains associated, but no synthetic source span is added.
      if (original.entry()
              .project()
              .sources()[location.source.source.index]
              .origin != SourceOrigin::Installation)
        locations[{location.line, location.column}].push_back(location.source);
    }
    for (const auto &item : *ast.getAsObject()->getArray("declarations")) {
      const auto &declaration = *item.getAsObject();
      auto owner = *declaration.getString("owner");
      for (const auto &item : *declaration.getArray("nodes")) {
        const auto &node = *item.getAsObject();
        const auto &path = *node.getArray("path");
        if (path.size() > limits.parseDepth + limits.expressionDepth)
          return error("source.limit",
                       "source association path depth exceeded");
        if (auto e = charge(1 + owner.size() + 2 * path.size()))
          return std::move(e);
        written[key(*node.getObject("span"))].push_back(
            json::Object{{"owner", owner.str()}, {"path", *node.get("path")}});
      }
    }
    json::Array result;
    for (const auto &row : rows) {
      if (auto e = charge(1 + row.row.size() + row.operation.size()))
        return std::move(e);
      json::Array coordinate;
      for (auto index : row.row)
        coordinate.push_back(index);
      json::Value range = nullptr;
      json::Array sources;
      if (row.original) {
        const auto &position = *row.original;
        range = json::Object{{"begin", position.begin},
                             {"end", position.end},
                             {"line", position.line},
                             {"column", position.column}};
        auto found = locations.find({position.line, position.column});
        if (found != locations.end())
          for (auto location : found->second) {
            if (auto e = charge(1))
              return std::move(e);
            auto source = span(location);
            json::Array candidates;
            auto selected = written.find(key(source));
            if (selected != written.end())
              for (const auto &candidate : selected->second) {
                const auto &address = *candidate.getAsObject();
                if (auto e = charge(1 + address.getString("owner")->size() +
                                    2 * address.getArray("path")->size()))
                  return std::move(e);
                candidates.push_back(candidate);
              }
            sources.push_back(
                json::Object{{"span", std::move(source)},
                             {"candidates", std::move(candidates)}});
          }
      }
      result.push_back(
          json::Object{{"row", std::move(coordinate)},
                       {"operation", row.operation},
                       {"derivation", derivation(row.derivation).str()},
                       {"original", std::move(range)},
                       {"sources", std::move(sources)}});
    }
    return result;
  }
};
// Definition name to the nonempty sites of its block, including nested
// regions and stop terminators.
using SnapshotSites = std::map<std::string, std::set<std::string>>;
Error blockSites(const json::Value &value, std::set<std::string> &sites,
                 unsigned depth) {
  const auto *block = value.getAsArray();
  if (depth > 256 || !block || block->size() != 3 ||
      (*block)[0] != json::Value("block") || !(*block)[1].getAsArray())
    return error("source.correspondence.export", "snapshot block differs");
  for (const auto &item : *(*block)[1].getAsArray()) {
    const auto *instruction = item.getAsArray();
    if (!instruction || instruction->size() != 5 ||
        !(*instruction)[3].getAsArray() || !(*instruction)[4].getAsString())
      return error("source.correspondence.export",
                   "snapshot instruction differs");
    if (!(*instruction)[4].getAsString()->empty())
      sites.insert((*instruction)[4].getAsString()->str());
    for (const auto &region : *(*instruction)[3].getAsArray()) {
      const auto *parts = region.getAsArray();
      if (!parts || parts->size() != 3)
        return error("source.correspondence.export", "snapshot region differs");
      if (auto e = blockSites((*parts)[2], sites, depth + 1))
        return e;
    }
  }
  const auto *terminator = (*block)[2].getAsArray();
  if (terminator && terminator->size() == 3 &&
      (*terminator)[0] == json::Value("stop") && (*terminator)[2].getAsString())
    sites.insert((*terminator)[2].getAsString()->str());
  return Error::success();
}
Expected<SnapshotSites> snapshotSites(const json::Value &snapshot) {
  SnapshotSites result;
  const auto *tables = snapshot.getAsArray();
  if (!tables || tables->size() != 11)
    return error("source.correspondence.export", "snapshot tables differ");
  for (unsigned table : {4, 5, 6, 7}) {
    const auto *rows = (*tables)[table].getAsArray();
    if (!rows)
      return error("source.correspondence.export", "snapshot tables differ");
    for (const auto &item : *rows) {
      const auto *row = item.getAsArray();
      if (!row || row->size() < 2 || !(*row)[1].getAsString())
        return error("source.correspondence.export", "snapshot row differs");
      auto &sites = result[(*row)[1].getAsString()->str()];
      const auto *body = row->back().getAsArray();
      if (body && !body->empty() && (*body)[0] == json::Value("block"))
        if (auto e = blockSites(row->back(), sites, 0))
          return std::move(e);
    }
  }
  return result;
}
} // namespace
Error checkCorrespondenceInventory(const json::Value &value) {
  auto fail = [](const Twine &message) {
    return error("source.correspondence.export", message.str());
  };
  const auto *document = value.getAsObject();
  const auto *instances =
      document && document->getObject("instances")
          ? document->getObject("instances")->getArray("instances")
          : nullptr;
  const auto *generated = document ? document->getArray("generated") : nullptr;
  const auto *occurrences =
      document ? document->getArray("occurrences") : nullptr;
  const auto *rows = document ? document->getArray("rows") : nullptr;
  const auto *snapshot = document ? document->get("snapshot") : nullptr;
  if (!instances || !generated || !occurrences || !rows || !snapshot ||
      !snapshot->getAsArray() || snapshot->getAsArray()->size() != 11)
    return fail("correspondence inventory members differ");
  auto sites = snapshotSites(*snapshot);
  if (!sites)
    return sites.takeError();
  std::map<std::string, unsigned> owners;
  for (const auto &item : *instances) {
    auto symbol = item.getAsObject() ? item.getAsObject()->getString("symbol")
                                     : std::nullopt;
    if (!symbol)
      return fail("instance symbol is absent");
    ++owners[symbol->str()];
  }
  std::set<std::pair<std::string, std::string>> occurred;
  for (const auto &item : *occurrences) {
    const auto *occurrence = item.getAsObject();
    auto definition =
        occurrence ? occurrence->getString("definition") : std::nullopt;
    auto site = occurrence ? occurrence->getString("site") : std::nullopt;
    auto found = definition ? sites->find(definition->str()) : sites->end();
    if (!definition || !site || !occurrence->getArray("nodes") ||
        found == sites->end() || !found->second.count(site->str()))
      return fail("occurrence names no snapshot site");
    if (!occurred.emplace(definition->str(), site->str()).second)
      return fail("occurrence repeats a site");
  }
  std::set<std::string> provenance;
  for (const auto &item : *generated) {
    const auto *entry = item.getAsObject();
    auto symbol = entry ? entry->getString("symbol") : std::nullopt;
    auto purpose = entry ? entry->getString("purpose") : std::nullopt;
    auto part = entry ? entry->getString("part") : std::nullopt;
    const auto *origins = entry ? entry->getArray("origins") : nullptr;
    if (!symbol || !purpose || !part || !origins ||
        (*purpose != "control" && *purpose != "custody" &&
         *purpose != "finite" && *purpose != "map"))
      return fail("generated definition shape differs");
    ++owners[symbol->str()];
    std::optional<std::pair<std::string, std::string>> previous;
    for (const auto &origin : *origins) {
      const auto *pair = origin.getAsObject();
      auto definition = pair ? pair->getString("definition") : std::nullopt;
      auto site = pair ? pair->getString("site") : std::nullopt;
      if (!definition || !site)
        return fail("generated origin shape differs");
      // A pure mathematical instruction publishes no site, so an origin
      // names the definition and the emitter's site there.
      std::pair<std::string, std::string> key{definition->str(), site->str()};
      if ((previous && !(*previous < key)) || site->empty() ||
          !sites->count(key.first))
        return fail("generated origins are unsorted, repeated or outside "
                    "the snapshot");
      previous = std::move(key);
    }
    if (origins->empty() || !provenance
                                 .insert(printJson(json::Array{
                                     *purpose, *part, *entry->get("origins")}))
                                 .second)
      return fail("generated purpose, part and origins repeat");
  }
  std::set<std::pair<int64_t, int64_t>> computed;
  for (const auto &item : *rows) {
    const auto *row = item.getAsObject();
    const auto *coordinate = row ? row->getArray("row") : nullptr;
    if (row && coordinate && coordinate->size() == 2 &&
        row->getString("derivation") == "computation")
      computed.emplace((*coordinate)[0].getAsInteger().value_or(-1),
                       (*coordinate)[1].getAsInteger().value_or(-1));
  }
  const auto &tables = *snapshot->getAsArray();
  for (unsigned table : {4, 7})
    for (unsigned i = 0; i < tables[table].getAsArray()->size(); ++i) {
      const auto &row = *(*tables[table].getAsArray())[i].getAsArray();
      auto kind = row[0].getAsString();
      auto symbol = row[1].getAsString()->str();
      if (table == 4 || kind == "function" || kind == "oracle") {
        if (owners[symbol] != 1)
          return fail("definition row " + symbol +
                      " is not exactly one instance or generated definition");
      } else if (kind == "realize" || kind == "finite" || kind == "collect" ||
                 kind == "map") {
        if (!computed.count({table, i}))
          return fail("computation row " + symbol + " has no association");
      } else
        return fail("definition row " + symbol + " has no inventory");
    }
  for (const auto &[symbol, count] : owners)
    if (count > 1)
      return fail("symbol " + symbol + " repeats in the inventory");
  return Error::success();
}
static Expected<json::Value> correspondenceData(const CheckedOriginal &original,
                                                const Limits &limits) {
  if (auto e = checkLimits(limits))
    return std::move(e);
  const auto &entry = original.entry();
  if (!entry.protocolOrNull())
    return error(
        "source.correspondence.export",
        "structured source correspondence requires a protocol subject");
  if (original.bytes().size() > limits.irBytes ||
      original.interfaceJson().size() > limits.interfaceBytes)
    return error("source.limit", "checked original exceeds export byte limits");
  auto ast = writtenSourceData(entry.project(), limits);
  if (!ast)
    return ast.takeError();
  auto bindings = sourceBindingsData(entry.project(), limits);
  if (!bindings)
    return bindings.takeError();
  auto structured = detail::OriginalAccess::read(original);
  if (!structured)
    return structured.takeError();
  auto publication = protocol::publishSource(*structured);
  if (!publication)
    return publication.takeError();
  auto &snapshot = publication->snapshot;
  auto instances = sourceInstancesData(entry, limits);
  if (!instances)
    return instances.takeError();
  // Symbols select actual rows of this snapshot, never a decoded name/hash.
  std::map<std::string, json::Array> definitions;
  uint64_t remaining = limits.work;
  auto charge = [&](uint64_t amount) -> bool {
    if (amount > remaining)
      return false;
    remaining -= amount;
    return true;
  };
  for (unsigned table : {4, 5, 6, 7}) {
    const auto &rows = *(*snapshot.getAsArray())[table].getAsArray();
    for (unsigned i = 0; i < rows.size(); ++i) {
      auto symbol = *(*rows[i].getAsArray())[1].getAsString();
      if (!charge(1 + symbol.size()))
        return error("source.limit", "instance row association limit exceeded");
      definitions[symbol.str()].push_back(json::Array{table, i});
    }
  }
  json::Array instanceRows;
  const auto &instanceList = *instances->getAsObject()->getArray("instances");
  for (unsigned i = 0; i < instanceList.size(); ++i) {
    auto symbol = *instanceList[i].getAsObject()->getString("symbol");
    if (!charge(1 + symbol.size()))
      return error("source.limit", "instance row association limit exceeded");
    auto found = definitions.find(symbol.str());
    json::Array selected;
    if (found != definitions.end()) {
      if (!charge(found->second.size()))
        return error("source.limit", "instance row association limit exceeded");
      selected = found->second;
    }
    instanceRows.push_back(
        json::Object{{"instance", i}, {"rows", std::move(selected)}});
  }
  // Generated definitions and site expressions are emission's record of these
  // exact bytes; the snapshot only orders the sites it publishes.
  const auto &emission = detail::OriginalAccess::emission(original);
  json::Array generated, generatedRows;
  for (unsigned i = 0; i < emission.generated.size(); ++i) {
    const auto &definition = emission.generated[i];
    json::Array origins;
    for (const auto &[from, site] : definition.origins) {
      if (!charge(2 + from.size() + site.size()))
        return error("source.limit", "generated definition limit exceeded");
      origins.push_back(json::Object{{"definition", from}, {"site", site}});
    }
    if (!charge(3 + definition.symbol.size() + definition.part.size()))
      return error("source.limit", "generated definition limit exceeded");
    generated.push_back(json::Object{{"symbol", definition.symbol},
                                     {"purpose", definition.purpose},
                                     {"part", definition.part},
                                     {"origins", std::move(origins)}});
    auto found = definitions.find(definition.symbol);
    json::Array selected;
    if (found != definitions.end()) {
      if (!charge(found->second.size()))
        return error("source.limit",
                     "generated row association limit exceeded");
      selected = found->second;
    }
    generatedRows.push_back(
        json::Object{{"generated", i}, {"rows", std::move(selected)}});
  }
  std::map<std::pair<std::string, std::string>, const EmittedSite *> emitted;
  for (const auto &site : emission.sites)
    emitted.emplace(std::make_pair(site.definition, site.site), &site);
  std::vector<EmittedSite> ordered;
  std::function<Error(StringRef, const protocol::SourceBlock &, unsigned)>
      walk = [&](StringRef definition, const protocol::SourceBlock &block,
                 unsigned depth) -> Error {
    auto add = [&](StringRef site) -> Error {
      if (!charge(1 + site.size()))
        return error("source.limit", "occurrence limit exceeded");
      auto found = emitted.find({definition.str(), site.str()});
      if (found == emitted.end())
        return error("source.correspondence.export",
                     "site " + site + " of " + definition +
                         " has no emission record");
      ordered.push_back(*found->second);
      return Error::success();
    };
    if (depth > limits.parseDepth + limits.expressionDepth)
      return error("source.limit", "occurrence nesting limit exceeded");
    for (const auto &instruction : block.instructions) {
      if (!instruction.site.empty())
        if (auto e = add(instruction.site))
          return e;
      for (const auto &region : instruction.regions)
        if (auto e = walk(definition, region, depth + 1))
          return e;
    }
    if (block.terminator == protocol::SourceTerminator::Stop && block.terminal)
      if (auto site = block.terminal->getAttrOfType<mlir::StringAttr>("site"))
        if (!site.getValue().empty())
          return add(site.getValue());
    return Error::success();
  };
  for (const auto &definition : structured->definitions)
    if (definition.hasBody)
      if (auto e = walk(definition.name, definition.body, 0))
        return std::move(e);
  auto nodes = writtenSiteNodes(entry.project(), ordered, limits);
  if (!nodes)
    return nodes.takeError();
  json::Array occurrences;
  for (unsigned i = 0; i < ordered.size(); ++i) {
    // An expression always has written nodes; only a site without one may
    // have none.
    if (ordered[i].expression && (*nodes)[i].empty())
      return error("source.correspondence.export",
                   "site " + ordered[i].site + " of " + ordered[i].definition +
                       " has an expression without written nodes");
    occurrences.push_back(json::Object{{"definition", ordered[i].definition},
                                       {"site", ordered[i].site},
                                       {"nodes", std::move((*nodes)[i])}});
  }
  auto rows =
      Associations(original, limits).run(*ast, publication->associations);
  if (!rows)
    return rows.takeError();
  json::Value document =
      json::Object{{"format", "zkc.source-correspondence/0"},
                   {"admission", detail::sourceAdmission(original)},
                   {"source_ast", std::move(*ast)},
                   {"bindings", std::move(*bindings)},
                   {"instances", std::move(*instances)},
                   {"instance_rows", std::move(instanceRows)},
                   {"generated", std::move(generated)},
                   {"generated_rows", std::move(generatedRows)},
                   {"occurrences", std::move(occurrences)},
                   {"snapshot", std::move(snapshot)},
                   {"rows", std::move(*rows)}};
  if (auto e = checkCorrespondenceInventory(document))
    return std::move(e);
  if (!jsonWithinByteLimit(document, limits.apiInspectionBytes))
    return error("source.limit",
                 "source correspondence export byte limit exceeded");
  ownJsonStrings(document);
  return document;
}
Expected<std::string>
exportSourceCorrespondence(const CheckedOriginal &original,
                           const Limits &limits) {
  auto data = correspondenceData(original, limits);
  if (!data)
    return data.takeError();
  return printJson(*data);
}
Error checkSourceCorrespondenceExport(const CheckedOriginal &original,
                                      StringRef bytes, const Limits &limits) {
  auto actual = zkc::parseNaturalJson(
      bytes, limits.apiInspectionBytes, limits.expressionDepth * 4 + 32,
      "source.correspondence.export", "source.limit");
  if (!actual)
    return actual.takeError();
  auto expected = correspondenceData(original, limits);
  if (!expected)
    return expected.takeError();
  if (!zkc::equalNaturalJson(*actual, *expected))
    return error("source.correspondence.export",
                 "publication differs from the checked source export");
  return Error::success();
}
} // namespace zkc::language
