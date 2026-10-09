#include "BundleInternal.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"
#include <algorithm>
#include <set>

using namespace llvm;
namespace zkc::relation {
using namespace bundle;

namespace {
std::vector<uint32_t> groupsWith(const BundleTable &table,
                                 BundleAuthority authority) {
  std::vector<uint32_t> result;
  for (uint32_t i = 0; i < table.groups.size(); ++i)
    if (table.groups[i].authority == authority)
      result.push_back(i);
  return result;
}
Expected<std::vector<BundleColumns>> readGroups(const json::Value &value,
                                                const BundleTable &table,
                                                BundleAuthority authority,
                                                uint64_t &budget) {
  auto *array = value.getAsArray();
  if (!array)
    return zkc::error("bundle-data-schema", table.name);
  auto indices = groupsWith(table, authority);
  if (array->size() != indices.size())
    return zkc::error("bundle-group-count", table.name);
  std::vector<BundleColumns> result;
  for (size_t i = 0; i < indices.size(); ++i) {
    auto degree = bundleFieldDegree(table.groups[indices[i]].field);
    if (!degree)
      return degree.takeError();
    auto columns = readGroupValues((*array)[i], *degree, budget);
    if (!columns)
      return withDetail(columns.takeError(), table.name);
    result.push_back(std::move(*columns));
  }
  return result;
}
json::Value encodeGroups(const BundleTable &table, BundleAuthority authority,
                         ArrayRef<BundleColumns> groups) {
  auto indices = groupsWith(table, authority);
  json::Array result;
  for (size_t i = 0; i < groups.size(); ++i) {
    unsigned degree = 1;
    if (i < indices.size()) {
      auto known = bundleFieldDegree(table.groups[indices[i]].field);
      if (known)
        degree = *known;
      else
        consumeError(known.takeError());
    }
    result.push_back(encodeGroupValues(groups[i], degree));
  }
  return result;
}
Expected<std::optional<uint32_t>> readHeightValue(const json::Value &value) {
  if (value.kind() == json::Value::Null)
    return std::optional<uint32_t>();
  auto height = natural(value, BundleLimits::height);
  if (!height)
    return zkc::error("bundle-height");
  return std::optional<uint32_t>(uint32_t(*height));
}
json::Value encodeHeightValue(std::optional<uint32_t> height) {
  return height ? json::Value(*height) : json::Value(nullptr);
}
const json::Array *dataRoot(const json::Value &value, size_t arity,
                            StringRef tag, const Bundle &bundle,
                            std::string &relation) {
  auto *root = row(value, arity, tag);
  if (!root)
    return nullptr;
  auto text = (*root)[1].getAsString();
  auto *tables = (*root)[arity - 1].getAsArray();
  if (!text || !tables || tables->size() != bundle.tables().size())
    return nullptr;
  relation = text->str();
  return tables;
}
} // namespace

Expected<json::Value> readBundleDataJson(StringRef text) {
  return zkc::parseNaturalJson(text, BundleLimits::dataBytes, 16,
                               "bundle-data-schema", "bundle-data-limit");
}

Expected<BundleConfiguration>
readBundleConfiguration(const Bundle &bundle, const json::Value &value) {
  BundleConfiguration result;
  auto *tables = dataRoot(value, 3, "zkc.relation-configuration/0", bundle,
                          result.relation);
  if (!tables)
    return zkc::error("bundle-data-schema");
  uint64_t budget = BundleLimits::coordinates;
  for (size_t t = 0; t < tables->size(); ++t) {
    const auto &table = bundle.tables()[t];
    auto *entry = row((*tables)[t], 2);
    if (!entry)
      return zkc::error("bundle-data-schema", table.name);
    auto height = readHeightValue((*entry)[0]);
    if (!height)
      return withDetail(height.takeError(), table.name);
    auto groups =
        readGroups((*entry)[1], table, BundleAuthority::Config, budget);
    if (!groups)
      return groups.takeError();
    result.tables.push_back({*height, std::move(*groups)});
  }
  return result;
}

Expected<BundleInstance> readBundleInstance(const Bundle &bundle,
                                            const json::Value &value) {
  BundleInstance result;
  auto *tables =
      dataRoot(value, 4, "zkc.relation-instance/0", bundle, result.relation);
  if (!tables)
    return zkc::error("bundle-data-schema");
  std::vector<std::string> fields;
  for (const auto &slot : bundle.publics())
    fields.push_back(slot.field);
  auto publics = readValues((*value.getAsArray())[2], fields);
  if (!publics)
    return publics.takeError();
  result.publics = std::move(*publics);
  uint64_t budget = BundleLimits::coordinates;
  for (size_t t = 0; t < tables->size(); ++t) {
    const auto &table = bundle.tables()[t];
    if (row((*tables)[t], 1, "absent")) {
      result.tables.push_back({false, std::nullopt, {}});
      continue;
    }
    auto *entry = row((*tables)[t], 3, "present");
    if (!entry)
      return zkc::error("bundle-data-schema", table.name);
    auto height = readHeightValue((*entry)[1]);
    if (!height)
      return withDetail(height.takeError(), table.name);
    auto groups =
        readGroups((*entry)[2], table, BundleAuthority::Public, budget);
    if (!groups)
      return groups.takeError();
    result.tables.push_back({true, *height, std::move(*groups)});
  }
  return result;
}

Expected<BundleWitness> readBundleWitness(const Bundle &bundle,
                                          const json::Value &value) {
  BundleWitness result;
  auto *tables =
      dataRoot(value, 3, "zkc.relation-witness/0", bundle, result.relation);
  if (!tables)
    return zkc::error("bundle-data-schema");
  uint64_t budget = BundleLimits::coordinates;
  for (size_t t = 0; t < tables->size(); ++t) {
    if ((*tables)[t].kind() == json::Value::Null) {
      result.tables.push_back(std::nullopt);
      continue;
    }
    auto groups = readGroups((*tables)[t], bundle.tables()[t],
                             BundleAuthority::Witness, budget);
    if (!groups)
      return groups.takeError();
    result.tables.push_back(std::move(*groups));
  }
  return result;
}

json::Value encodeBundleConfiguration(const Bundle &bundle,
                                      const BundleConfiguration &data) {
  json::Array tables;
  for (size_t t = 0; t < data.tables.size() && t < bundle.tables().size(); ++t)
    tables.push_back(
        json::Array{encodeHeightValue(data.tables[t].height),
                    encodeGroups(bundle.tables()[t], BundleAuthority::Config,
                                 data.tables[t].groups)});
  return json::Array{"zkc.relation-configuration/0", data.relation,
                     std::move(tables)};
}
json::Value encodeBundleInstance(const Bundle &bundle,
                                 const BundleInstance &data) {
  json::Array publics, tables;
  for (const auto &value : data.publics)
    publics.push_back(encodeValue(value));
  for (size_t t = 0; t < data.tables.size() && t < bundle.tables().size();
       ++t) {
    const auto &table = data.tables[t];
    if (!table.present)
      tables.push_back(json::Array{"absent"});
    else
      tables.push_back(
          json::Array{"present", encodeHeightValue(table.height),
                      encodeGroups(bundle.tables()[t], BundleAuthority::Public,
                                   table.groups)});
  }
  return json::Array{"zkc.relation-instance/0", data.relation,
                     std::move(publics), std::move(tables)};
}
json::Value encodeBundleWitness(const Bundle &bundle,
                                const BundleWitness &data) {
  json::Array tables;
  for (size_t t = 0; t < data.tables.size() && t < bundle.tables().size(); ++t)
    tables.push_back(data.tables[t] ? encodeGroups(bundle.tables()[t],
                                                   BundleAuthority::Witness,
                                                   *data.tables[t])
                                    : json::Value(nullptr));
  return json::Array{"zkc.relation-witness/0", data.relation,
                     std::move(tables)};
}

namespace bundle {
namespace {
std::vector<int32_t> offsets(const std::vector<BundleOutputFact> &facts,
                             ArrayRef<uint32_t> outputs) {
  std::vector<int32_t> result;
  for (uint32_t output : outputs)
    for (const auto &read : facts[output].reads)
      result.push_back(read.offset);
  return result;
}
std::vector<uint32_t> interactionOutputs(const BundleInteraction &interaction) {
  std::vector<uint32_t> outputs = interaction.tuple;
  outputs.push_back(interaction.count);
  return outputs;
}
} // namespace

Expected<Admitted> admitData(const Bundle &bundle,
                             const BundleConfiguration &config,
                             const BundleInstance &instance,
                             const BundleWitness &witness, Fields &fields,
                             StringRef identity) {
  if (config.relation != identity || instance.relation != identity ||
      witness.relation != identity)
    return zkc::error("bundle-relation");
  auto tables = bundle.tables();
  if (config.tables.size() != tables.size() ||
      instance.tables.size() != tables.size() ||
      witness.tables.size() != tables.size())
    return zkc::error("bundle-data-shape");
  if (instance.publics.size() != bundle.publics().size())
    return zkc::error("bundle-public-shape");
  Admitted result;
  result.tables.resize(tables.size());
  std::vector<uint32_t> configHeights(tables.size(), 0);
  uint64_t coordinates = 0;
  // Shape, presence, height authority and exact lengths; no value is parsed.
  for (size_t t = 0; t < tables.size(); ++t) {
    const auto &table = tables[t];
    const auto &cfg = config.tables[t];
    const auto &ins = instance.tables[t];
    const auto &wit = witness.tables[t];
    auto context = [&](StringRef code) { return zkc::error(code, table.name); };
    bool present = ins.present;
    if (!present && !table.optional)
      return context("bundle-table-missing");
    if (!present && (ins.height || !ins.groups.empty()))
      return context("bundle-absent-data");
    if (present != wit.has_value())
      return context("bundle-witness-presence");
    const auto &policy = table.height;
    uint32_t height = 0;
    switch (policy.authority) {
    case BundleHeightAuthority::Fixed:
      if (cfg.height || ins.height)
        return context("bundle-height-authority");
      height = policy.min;
      configHeights[t] = height;
      break;
    case BundleHeightAuthority::Config:
      if (!cfg.height || ins.height)
        return context("bundle-height-authority");
      height = *cfg.height;
      configHeights[t] = height;
      break;
    case BundleHeightAuthority::Instance:
      if (cfg.height || (present && !ins.height))
        return context("bundle-height-authority");
      height = present ? *ins.height : 0;
      break;
    }
    bool checked =
        policy.authority != BundleHeightAuthority::Instance || present;
    if (checked && (height < policy.min || height > policy.max ||
                    (policy.powerOfTwo && !isPowerOf2_32(height))))
      return context("bundle-height");
    auto configGroups = groupsWith(table, BundleAuthority::Config);
    auto publicGroups = groupsWith(table, BundleAuthority::Public);
    auto witnessGroups = groupsWith(table, BundleAuthority::Witness);
    if (cfg.groups.size() != configGroups.size() ||
        (present && (ins.groups.size() != publicGroups.size() ||
                     wit->size() != witnessGroups.size())))
      return context("bundle-group-count");
    auto length = [&](uint32_t group, uint32_t rows) -> Expected<uint64_t> {
      auto degree = bundleFieldDegree(table.groups[group].field);
      if (!degree)
        return degree.takeError();
      return uint64_t(rows) * table.groups[group].width * *degree;
    };
    auto checkLength = [&](ArrayRef<uint32_t> indices,
                           ArrayRef<BundleColumns> groups,
                           uint32_t rows) -> Error {
      for (size_t i = 0; i < indices.size(); ++i) {
        auto expected = length(indices[i], rows);
        if (!expected)
          return expected.takeError();
        // The declared height and width bound the data before its length is
        // compared, so an oversized shape refuses without supplied values.
        coordinates += *expected;
        if (coordinates > BundleLimits::coordinates)
          return context("bundle-data-limit");
        if (groups[i].size() != *expected)
          return context("bundle-group-shape");
      }
      return Error::success();
    };
    if (auto error = checkLength(configGroups, cfg.groups, configHeights[t]))
      return error;
    if (present) {
      if (auto error = checkLength(publicGroups, ins.groups, height))
        return error;
      if (auto error = checkLength(witnessGroups, *wit, height))
        return error;
    }
    result.tables[t].present = present;
    result.tables[t].height = present ? height : 0;
  }
  // Every read domain is checked from syntax before any arithmetic, so a
  // product with zero cannot hide an undefined read.
  uint64_t work = 0, contributions = 0;
  for (size_t t = 0; t < tables.size(); ++t) {
    if (!result.tables[t].present)
      continue;
    const auto &table = tables[t];
    const auto &facts = bundle.facts()[t];
    uint32_t height = result.tables[t].height;
    for (const auto &assertion : table.assertions)
      if (auto error = windowAt(assertion.scope, table.readModel, height,
                                offsets(facts, {assertion.output})))
        return withDetail(std::move(error), table.name);
    for (const auto &interaction : table.interactions) {
      if (auto error =
              windowAt(interaction.scope, table.readModel, height,
                       offsets(facts, interactionOutputs(interaction))))
        return withDetail(std::move(error), table.name);
      auto [lo, hi] = scopeRows(interaction.scope, height);
      contributions += hi > lo ? hi - lo : 0;
    }
    size_t checks = table.assertions.size() + table.interactions.size();
    if (checks)
      work += uint64_t(height) * (table.arena.nodes().size() +
                                  table.arena.inputs().size() + checks + 1);
    if (work > BundleLimits::work)
      return zkc::error("bundle-work-limit", table.name);
    if (contributions > BundleLimits::contributions)
      return zkc::error("bundle-contribution-limit", table.name);
  }
  result.work = work;
  // Canonical value parsing, bounded by the coordinate count above.
  for (size_t i = 0; i < instance.publics.size(); ++i) {
    auto arithmetic = fields.get(bundle.publics()[i].field);
    if (!arithmetic)
      return arithmetic.takeError();
    auto value = (*arithmetic)->parse(instance.publics[i]);
    if (!value)
      return withDetail(value.takeError(), bundle.publics()[i].name);
    result.publics.push_back(std::move(*value));
  }
  for (size_t t = 0; t < tables.size(); ++t) {
    const auto &table = tables[t];
    auto &admitted = result.tables[t];
    admitted.groups.resize(table.groups.size());
    size_t next[3] = {0, 0, 0};
    for (size_t g = 0; g < table.groups.size(); ++g) {
      const auto &group = table.groups[g];
      const BundleColumns *columns = nullptr;
      uint32_t rows = admitted.height;
      switch (group.authority) {
      case BundleAuthority::Config:
        columns = &config.tables[t].groups[next[0]++];
        rows = configHeights[t];
        break;
      case BundleAuthority::Public:
        if (admitted.present)
          columns = &instance.tables[t].groups[next[1]++];
        break;
      case BundleAuthority::Witness:
        if (admitted.present)
          columns = &(*witness.tables[t])[next[2]++];
        break;
      }
      if (!columns)
        continue;
      auto arithmetic = fields.get(group.field);
      if (!arithmetic)
        return arithmetic.takeError();
      std::vector<APInt> parsed;
      if (auto error = checkColumns(*columns, uint64_t(rows) * group.width,
                                    **arithmetic, parsed))
        return withDetail(std::move(error), table.name + "." + group.name);
      // Configuration data of an absent table is admitted but never read.
      if (admitted.present)
        admitted.groups[g] = std::move(parsed);
    }
  }
  return result;
}
} // namespace bundle

Error Bundle::admit(const BundleConfiguration &config,
                    const BundleInstance &instance,
                    const BundleWitness &witness) const {
  Fields fields;
  auto admitted =
      admitData(*this, config, instance, witness, fields, identity_);
  if (!admitted)
    return admitted.takeError();
  return Error::success();
}

namespace {
struct Check {
  bool assertion;
  uint32_t index;
  uint32_t lo, hi;
};
struct BalanceKey {
  uint32_t channel;
  bool local;
  uint32_t table, key;
  std::string tuple;
  bool operator<(const BalanceKey &other) const {
    return std::tie(channel, local, table, key, tuple) <
           std::tie(other.channel, other.local, other.table, other.key,
                    other.tuple);
  }
};
struct Accumulator {
  BundleBalance balance;
  Scalar sum;
  const Arithmetic *arithmetic = nullptr;
};
} // namespace

Expected<BundleEvaluation>
Bundle::evaluate(const BundleConfiguration &config,
                 const BundleInstance &instance,
                 const BundleWitness &witness) const {
  Fields fields;
  auto admitted =
      admitData(*this, config, instance, witness, fields, identity_);
  if (!admitted)
    return admitted.takeError();
  BundleEvaluation result;
  result.work = admitted->work;
  std::map<BalanceKey, Accumulator> balances;
  std::map<std::pair<std::string, std::string>, Scalar> constants;
  for (uint32_t t = 0; t < tables_.size(); ++t) {
    const auto &state = admitted->tables[t];
    if (!state.present)
      continue;
    const auto &table = tables_[t];
    const auto &facts = facts_[t];
    uint32_t height = state.height;
    std::vector<Check> checks;
    std::set<uint32_t> boundaries{0, height};
    for (uint32_t i = 0; i < table.assertions.size(); ++i) {
      auto [lo, hi] = scopeRows(table.assertions[i].scope, height);
      checks.push_back({true, i, lo, hi});
    }
    for (uint32_t i = 0; i < table.interactions.size(); ++i) {
      auto [lo, hi] = scopeRows(table.interactions[i].scope, height);
      checks.push_back({false, i, lo, hi});
    }
    for (const auto &check : checks)
      if (check.lo < check.hi)
        boundaries.insert({check.lo, check.hi});
    std::vector<unsigned> degrees;
    for (const auto &group : table.groups) {
      auto degree = bundleFieldDegree(group.field);
      if (!degree)
        return degree.takeError();
      degrees.push_back(*degree);
    }
    std::vector<std::vector<BundleResidual>> residuals(table.assertions.size());
    std::vector<uint32_t> cuts(boundaries.begin(), boundaries.end());
    for (size_t s = 0; s + 1 < cuts.size(); ++s) {
      uint32_t from = cuts[s], to = cuts[s + 1];
      std::vector<const Check *> active;
      std::set<uint32_t> needed;
      for (const auto &check : checks) {
        if (check.lo > from || check.hi < to || check.lo >= check.hi)
          continue;
        active.push_back(&check);
        if (check.assertion)
          needed.insert(table.assertions[check.index].output);
        else
          for (uint32_t output :
               interactionOutputs(table.interactions[check.index]))
            needed.insert(output);
      }
      if (active.empty())
        continue;
      std::vector<uint32_t> positions(needed.begin(), needed.end());
      auto slot = [&](uint32_t output) {
        return llvm::lower_bound(positions, output) - positions.begin();
      };
      for (uint32_t r = from; r < to; ++r) {
        auto fetch = [&](uint32_t input) -> Expected<Scalar> {
          const auto &binding = table.inputs[input];
          if (binding.kind == BundleInput::Kind::Public)
            return admitted->publics[binding.index];
          const auto &group = table.groups[binding.index];
          return element(state.groups[binding.index], degrees[binding.index],
                         group.width,
                         readRow(table.readModel, height, r, binding.offset),
                         binding.column);
        };
        RowAlgebra algebra{fields, fetch, constants};
        auto values = table.arena.evaluate<Scalar>(positions, algebra);
        if (!values)
          return values.takeError();
        for (const Check *check : active) {
          if (check->assertion) {
            uint32_t output = table.assertions[check->index].output;
            auto arithmetic = fields.get(facts[output].field);
            if (!arithmetic)
              return arithmetic.takeError();
            const auto &value = (*values)[slot(output)];
            result.satisfied &= (*arithmetic)->isZero(value);
            residuals[check->index].push_back(
                {t, check->index, r, (*arithmetic)->print(value)});
            continue;
          }
          const auto &interaction = table.interactions[check->index];
          const auto &channel = channels_[interaction.channel];
          BalanceKey key{interaction.channel, interaction.locality.local,
                         interaction.locality.local ? t : 0,
                         interaction.locality.key, ""};
          std::vector<BundleColumns> tuple;
          json::Array printed;
          for (size_t i = 0; i < interaction.tuple.size(); ++i) {
            auto arithmetic = fields.get(channel.tuple[i]);
            if (!arithmetic)
              return arithmetic.takeError();
            tuple.push_back(
                (*arithmetic)->print((*values)[slot(interaction.tuple[i])]));
            printed.push_back(encodeValue(tuple.back()));
          }
          key.tuple = zkc::printJson(json::Value(std::move(printed)));
          auto counter = fields.get(channel.count);
          if (!counter)
            return counter.takeError();
          const auto &count = (*values)[slot(interaction.count)];
          auto [entry, inserted] = balances.try_emplace(key);
          if (inserted) {
            entry->second.balance.kind = channel.kind;
            entry->second.balance.channel = interaction.channel;
            if (interaction.locality.local)
              entry->second.balance.local =
                  std::make_pair(t, interaction.locality.key);
            entry->second.balance.tuple = std::move(tuple);
            entry->second.arithmetic = *counter;
            entry->second.sum = (*counter)->zero();
          }
          if (channel.kind == BundleChannelKind::FieldBalance) {
            entry->second.sum = (*counter)->add(entry->second.sum, count);
            continue;
          }
          // A multiplicity denotes its canonical natural representative; a
          // value above the declared bound makes the relation unsatisfied.
          auto n = (*counter)->natural(count);
          if (!n || *n > *interaction.bound) {
            result.satisfied = false;
            result.rangeFailures.push_back({t, check->index, r});
            continue;
          }
          (interaction.side == BundleSide::Push ? entry->second.balance.push
                                                : entry->second.balance.pull) +=
              *n;
        }
      }
    }
    for (auto &rows : residuals)
      llvm::append_range(result.residuals, rows);
  }
  for (auto &[key, accumulator] : balances) {
    auto &balance = accumulator.balance;
    if (balance.kind == BundleChannelKind::FieldBalance) {
      balance.balanced = accumulator.arithmetic->isZero(accumulator.sum);
      balance.sum = accumulator.arithmetic->print(accumulator.sum);
    } else {
      balance.balanced = balance.push == balance.pull;
    }
    result.satisfied &= balance.balanced;
    result.balances.push_back(std::move(balance));
  }
  return result;
}

json::Value BundleEvaluation::encode() const {
  json::Array residualRows, balanceRows, failureRows;
  for (const auto &r : residuals)
    residualRows.push_back(
        json::Array{r.table, r.assertion, r.row, encodeValue(r.value)});
  for (const auto &b : balances) {
    json::Array tuple;
    for (const auto &value : b.tuple)
      tuple.push_back(encodeValue(value));
    json::Value local =
        b.local ? json::Value(json::Array{b.local->first, b.local->second})
                : json::Value(nullptr);
    if (b.kind == BundleChannelKind::FieldBalance)
      balanceRows.push_back(json::Array{"field-balance", b.channel,
                                        std::move(local), std::move(tuple),
                                        encodeValue(b.sum), b.balanced});
    else
      balanceRows.push_back(json::Array{"multiset", b.channel, std::move(local),
                                        std::move(tuple), b.push, b.pull,
                                        b.balanced});
  }
  for (const auto &f : rangeFailures)
    failureRows.push_back(json::Array{f.table, f.interaction, f.row});
  return json::Object{{"satisfied", satisfied},
                      {"work", work},
                      {"residuals", std::move(residualRows)},
                      {"balances", std::move(balanceRows)},
                      {"range_failures", std::move(failureRows)}};
}

} // namespace zkc::relation
