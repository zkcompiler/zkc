#include "zkc/Transforms/OracleSelection.h"
#include "zkc/Support/BoundedStream.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <limits>
#include <set>
#include <tuple>

using namespace llvm;
namespace zkc::protocol {
namespace {
constexpr size_t byteLimit = 1024 * 1024;
constexpr StringLiteral invalid = "oracle-realization-selection";
constexpr StringLiteral limit = "oracle-realization-selection-limit";
bool validTable(const OracleTableRealization &table) {
  return json::isUTF8(table.scheme) && table.scheme.size() <= 4096 &&
         (table.grouping == OracleLeafGrouping::Individual ||
          table.grouping == OracleLeafGrouping::AntipodalPairs) &&
         (table.order == OracleLeafOrder::Natural ||
          table.order == OracleLeafOrder::BitReversed) &&
         (!table.scheme.empty() ||
          (table.grouping == OracleLeafGrouping::Individual &&
           table.order == OracleLeafOrder::Natural));
}
Expected<OracleTableRealization> readTable(const json::Object &object) {
  auto scheme = object.getString("scheme");
  auto grouping = object.getString("grouping");
  auto order = object.getString("order");
  if (!scheme || !grouping || !order ||
      (*grouping != "individual" && *grouping != "antipodal-pairs") ||
      (*order != "natural" && *order != "bit-reversed"))
    return error(invalid);
  OracleTableRealization table{
      scheme->str(),
      *grouping == "individual" ? OracleLeafGrouping::Individual
                                : OracleLeafGrouping::AntipodalPairs,
      *order == "natural" ? OracleLeafOrder::Natural
                          : OracleLeafOrder::BitReversed};
  if (!validTable(table))
    return error(invalid);
  return table;
}
json::Object tableObject(const OracleTableRealization &table) {
  return json::Object{
      {"scheme", table.scheme},
      {"grouping", table.grouping == OracleLeafGrouping::Individual
                       ? "individual"
                       : "antipodal-pairs"},
      {"order",
       table.order == OracleLeafOrder::Natural ? "natural" : "bit-reversed"}};
}
} // namespace
Error validateOracleRealizationPolicy(const OracleRealizationPolicy &policy) {
  if ((policy.order != OracleQueryOrder::Unrestricted &&
       policy.order != OracleQueryOrder::AfterFinalDraw) ||
      (policy.authentication != OracleAuthentication::PerQuery &&
       policy.authentication != OracleAuthentication::AtomicBlocks))
    return error(invalid);
  if (auto *uniform = std::get_if<OracleTableRealization>(&policy.roots)) {
    if (!validTable(*uniform))
      return error(invalid);
  } else {
    const auto &roots =
        std::get<std::vector<OracleRootSelection>>(policy.roots);
    if (roots.size() > 100000)
      return error(limit);
    std::set<std::pair<std::string, std::vector<unsigned>>> seen;
    for (const auto &root : roots) {
      if (root.entry.empty() || root.entry.size() > 4096 ||
          !json::isUTF8(root.entry) || root.path.empty() ||
          root.path.size() > 64 || !validTable(root.realization) ||
          !seen.emplace(root.entry, root.path).second)
        return error(invalid);
    }
  }
  return Error::success();
}
Expected<OracleRealizationPolicy> parseOracleRealizationPolicy(StringRef text) {
  auto value = parseNaturalJson(text, byteLimit, 32, invalid, limit);
  if (!value)
    return value.takeError();
  auto *object = value->getAsObject();
  if (!object || object->size() != 4 ||
      object->getString("format") != "zkc.oracle-selection/0")
    return error(invalid);
  auto *roots = object->getObject("roots");
  auto order = object->getString("order");
  auto authentication = object->getString("authentication");
  if (!roots || roots->size() != 2 || !order || !authentication ||
      (*order != "unrestricted" && *order != "after-final-draw") ||
      (*authentication != "per-query" && *authentication != "atomic-blocks"))
    return error(invalid);
  OracleRealizationPolicy policy;
  policy.order = *order == "unrestricted" ? OracleQueryOrder::Unrestricted
                                          : OracleQueryOrder::AfterFinalDraw;
  policy.authentication = *authentication == "per-query"
                              ? OracleAuthentication::PerQuery
                              : OracleAuthentication::AtomicBlocks;
  if (roots->getString("kind") == "uniform") {
    auto *table = roots->getObject("table");
    if (!table || table->size() != 3)
      return error(invalid);
    auto choice = readTable(*table);
    if (!choice)
      return choice.takeError();
    policy.roots = std::move(*choice);
  } else if (roots->getString("kind") == "exact") {
    auto *entries = roots->getArray("entries");
    if (!entries)
      return error(invalid);
    if (entries->size() > 100000)
      return error(limit);
    std::vector<OracleRootSelection> exact;
    for (const auto &value : *entries) {
      auto *entry = value.getAsObject();
      if (!entry || entry->size() != 5 || !entry->getString("entry") ||
          !entry->getArray("path"))
        return error(invalid);
      auto *path = entry->getArray("path");
      if (path->empty() || path->size() > 64)
        return error(invalid);
      auto table = readTable(*entry);
      if (!table)
        return table.takeError();
      OracleRootSelection root{
          entry->getString("entry")->str(), {}, std::move(*table)};
      for (const auto &value : *path) {
        auto ordinal = value.getAsUINT64();
        if (!ordinal || *ordinal > std::numeric_limits<unsigned>::max())
          return error(invalid);
        root.path.push_back(static_cast<unsigned>(*ordinal));
      }
      exact.push_back(std::move(root));
    }
    policy.roots = std::move(exact);
  } else {
    return error(invalid);
  }
  if (auto failure = validateOracleRealizationPolicy(policy))
    return std::move(failure);
  return policy;
}
Expected<json::Value>
encodeOracleRealizationPolicy(const OracleRealizationPolicy &policy) {
  if (auto failure = validateOracleRealizationPolicy(policy))
    return std::move(failure);
  json::Object roots;
  if (auto *uniform = std::get_if<OracleTableRealization>(&policy.roots)) {
    roots = json::Object{{"kind", "uniform"}, {"table", tableObject(*uniform)}};
  } else {
    auto exact = std::get<std::vector<OracleRootSelection>>(policy.roots);
    std::sort(exact.begin(), exact.end(), [](const auto &a, const auto &b) {
      return std::tie(a.entry, a.path) < std::tie(b.entry, b.path);
    });
    json::Array entries;
    for (const auto &root : exact) {
      auto object = tableObject(root.realization);
      object["entry"] = root.entry;
      json::Array path;
      for (auto ordinal : root.path)
        path.push_back(ordinal);
      object["path"] = std::move(path);
      entries.push_back(std::move(object));
    }
    roots = json::Object{{"kind", "exact"}, {"entries", std::move(entries)}};
  }
  json::Value result = json::Object{
      {"format", "zkc.oracle-selection/0"},
      {"roots", std::move(roots)},
      {"order", policy.order == OracleQueryOrder::Unrestricted
                    ? "unrestricted"
                    : "after-final-draw"},
      {"authentication", policy.authentication == OracleAuthentication::PerQuery
                             ? "per-query"
                             : "atomic-blocks"}};
  std::string text;
  BoundedStream stream(text, byteLimit);
  stream << result;
  if (stream.overflow())
    return error(limit);
  return result;
}
} // namespace zkc::protocol
