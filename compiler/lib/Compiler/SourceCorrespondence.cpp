#include "zkc/Compiler/SourceCorrespondence.h"
#include "SourceArtifacts.h"
#include "SourceView.h"
#include "zkc/Language/InspectionData.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <map>
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
} // namespace
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
  auto &snapshot = structured->publication;
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
  auto rows =
      Associations(original, limits).run(*ast, structured->associations);
  if (!rows)
    return rows.takeError();
  json::Value document =
      json::Object{{"format", "zkc.source-correspondence/0"},
                   {"admission", detail::sourceAdmission(original)},
                   {"source_ast", std::move(*ast)},
                   {"bindings", std::move(*bindings)},
                   {"instances", std::move(*instances)},
                   {"instance_rows", std::move(instanceRows)},
                   {"snapshot", std::move(snapshot)},
                   {"rows", std::move(*rows)}};
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
