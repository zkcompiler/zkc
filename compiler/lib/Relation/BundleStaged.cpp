#include "BundleInternal.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <set>

using namespace llvm;
namespace zkc::relation {
using namespace bundle;

namespace {
/// Field of the value an input binding denotes, or a refusal. `phase` is the
/// phase whose table (or the global arena, phase = phases.size()) uses it.
Expected<std::string> inputField(const Bundle &bundle,
                                 ArrayRef<StagedPhase> phases, uint32_t table,
                                 uint32_t phase, const StagedInput &input,
                                 bool global) {
  switch (input.kind) {
  case StagedInput::Kind::Public:
    if (input.phase || input.offset || input.column ||
        input.index >= bundle.publics().size())
      return zkc::error("staged-input");
    return bundle.publics()[input.index].field;
  case StagedInput::Kind::Read: {
    if (global)
      return zkc::error("staged-global-read");
    if (input.phase > phase)
      return zkc::error("staged-phase-order");
    if (input.offset > int32_t(BundleLimits::offset) ||
        input.offset < -int32_t(BundleLimits::offset))
      return zkc::error("staged-input");
    if (input.phase == 0) {
      const auto &groups = bundle.tables()[table].groups;
      if (input.index >= groups.size() ||
          input.column >= groups[input.index].width)
        return zkc::error("staged-input");
      return groups[input.index].field;
    }
    const auto &groups = phases[input.phase - 1].tables[table].groups;
    if (input.index >= groups.size() ||
        input.column >= groups[input.index].width)
      return zkc::error("staged-input");
    return groups[input.index].field;
  }
  case StagedInput::Kind::Challenge:
  case StagedInput::Kind::Claim: {
    if (input.offset || input.column || input.phase == 0)
      return zkc::error("staged-input");
    if (input.phase > phase)
      return zkc::error("staged-phase-order");
    const auto &slots = input.kind == StagedInput::Kind::Challenge
                            ? phases[input.phase - 1].challenges
                            : phases[input.phase - 1].claims;
    if (input.index >= slots.size())
      return zkc::error("staged-input");
    return slots[input.index].field;
  }
  }
  return zkc::error("staged-input");
}
Error checkInputs(const Bundle &bundle, ArrayRef<StagedPhase> phases,
                  uint32_t table, uint32_t phase, const ring::Expression &arena,
                  ArrayRef<StagedInput> inputs, bool global) {
  if (inputs.size() != arena.inputs().size())
    return zkc::error("staged-input-count");
  std::set<std::tuple<int, uint32_t, uint32_t, int32_t, uint32_t>> seen;
  for (size_t i = 0; i < inputs.size(); ++i) {
    auto field = inputField(bundle, phases, table, phase, inputs[i], global);
    if (!field)
      return field.takeError();
    if (*field != arena.inputs()[i].field)
      return zkc::error("staged-input-field");
    const auto &in = inputs[i];
    if (!seen.insert({int(in.kind), in.phase, in.index, in.offset, in.column})
             .second)
      return zkc::error("staged-duplicate-input");
  }
  return Error::success();
}
std::vector<int32_t> stagedOffsets(const ring::Expression &arena,
                                   ArrayRef<StagedInput> inputs,
                                   uint32_t output) {
  std::vector<int32_t> result;
  auto used = arena.usedInputs({output});
  if (!used) {
    consumeError(used.takeError());
    return result;
  }
  for (uint32_t input : *used)
    if (inputs[input].kind == StagedInput::Kind::Read)
      result.push_back(inputs[input].offset);
  return result;
}
json::Value encodeSlots(ArrayRef<BundleSlot> slots) {
  json::Array result;
  for (const auto &slot : slots)
    result.push_back(json::Array{slot.name, slot.field});
  return result;
}
json::Value encodeInput(const StagedInput &input) {
  switch (input.kind) {
  case StagedInput::Kind::Public:
    return json::Array{"public", input.index};
  case StagedInput::Kind::Read:
    return json::Array{"read", input.phase, input.index,
                       printOffset(input.offset), input.column};
  case StagedInput::Kind::Challenge:
    return json::Array{"challenge", input.phase, input.index};
  case StagedInput::Kind::Claim:
    return json::Array{"claim", input.phase, input.index};
  }
  llvm_unreachable("admitted staged input");
}
json::Value encodeInputs(ArrayRef<StagedInput> inputs) {
  json::Array result;
  for (const auto &input : inputs)
    result.push_back(encodeInput(input));
  return result;
}
} // namespace

StagedProgram::StagedProgram(std::string relation,
                             std::vector<StagedPhase> phases,
                             StagedGlobal global,
                             std::vector<StagedPremise> premises)
    : relation_(std::move(relation)), phases_(std::move(phases)),
      global_(std::move(global)), premises_(std::move(premises)) {}

Expected<StagedProgram>
StagedProgram::create(const Bundle &bundle, std::vector<StagedPhase> phases,
                      StagedGlobal global,
                      std::vector<StagedPremise> premises) {
  if (phases.empty())
    return zkc::error("staged-phases");
  if (phases.size() > BundleLimits::phases ||
      premises.size() > BundleLimits::premises)
    return zkc::error("staged-limit");
  std::set<std::string> slotNames;
  for (const auto &phase : phases) {
    if (phase.challenges.size() + phase.claims.size() > BundleLimits::slots)
      return zkc::error("staged-limit");
    for (const auto *slots : {&phase.challenges, &phase.claims})
      for (const auto &slot : *slots) {
        if (!validName(slot.name))
          return zkc::error("bundle-name", slot.name);
        if (!slotNames.insert(slot.name).second)
          return zkc::error("bundle-duplicate-name", slot.name);
        if (!installedField(slot.field))
          return zkc::error("bundle-field", slot.field);
        if (auto degree = bundleFieldDegree(slot.field); !degree)
          return degree.takeError();
      }
    if (phase.tables.size() != bundle.tables().size())
      return zkc::error("staged-tables");
  }
  // An output may exist only as the subject of a recorded premise.
  std::map<std::pair<uint32_t, uint32_t>, std::vector<uint32_t>> premiseOutputs;
  for (const auto &premise : premises)
    if (premise.kind != StagedPremise::Kind::CharacteristicExceeds)
      llvm::append_range(premiseOutputs[{premise.phase, premise.table}],
                         premise.outputs);
  for (uint32_t t = 0; t < bundle.tables().size(); ++t) {
    const auto &base = bundle.tables()[t];
    std::set<std::string> groupNames;
    for (const auto &group : base.groups)
      groupNames.insert(group.name);
    for (uint32_t p = 0; p < phases.size(); ++p) {
      const auto &table = phases[p].tables[t];
      auto context = [&](Error error) {
        return withDetail(std::move(error),
                          base.name + "@" + std::to_string(p + 1));
      };
      if (table.groups.size() > BundleLimits::groups ||
          table.assertions.size() > BundleLimits::checks)
        return context(zkc::error("staged-limit"));
      for (const auto &group : table.groups) {
        if (!validName(group.name))
          return zkc::error("bundle-name", group.name);
        if (!groupNames.insert(group.name).second)
          return zkc::error("bundle-duplicate-name", group.name);
        if (!installedField(group.field))
          return zkc::error("bundle-field", group.field);
        if (auto degree = bundleFieldDegree(group.field); !degree)
          return degree.takeError();
        if (group.width < 1 || group.width > BundleLimits::width)
          return context(zkc::error("bundle-width"));
      }
      if (auto error = checkInputs(bundle, phases, t, p + 1, table.arena,
                                   table.inputs, false))
        return context(std::move(error));
      std::vector<uint32_t> referenced;
      for (const auto &assertion : table.assertions) {
        if (auto error = checkScope(assertion.scope))
          return error;
        referenced.push_back(assertion.output);
      }
      auto subjects = premiseOutputs.find({p + 1, t});
      if (subjects != premiseOutputs.end())
        for (uint32_t output : subjects->second)
          if (output < table.arena.outputs().size())
            referenced.push_back(output);
      if (auto error = checkOutputsUsed(table.arena, referenced))
        return context(std::move(error));
      if (base.readModel == BundleReadModel::Finite)
        for (const auto &assertion : table.assertions)
          for (int32_t offset :
               stagedOffsets(table.arena, table.inputs, assertion.output))
            if (!staticWindow(assertion.scope, offset))
              return context(zkc::error("bundle-window"));
    }
  }
  if (auto error = checkInputs(bundle, phases, 0, phases.size(), global.arena,
                               global.inputs, true))
    return withDetail(std::move(error), "global");
  if (auto error = checkOutputsUsed(global.arena, global.assertions))
    return withDetail(std::move(error), "global");
  for (const auto &premise : premises) {
    auto arenaOf = [&](uint32_t phase,
                       uint32_t table) -> const ring::Expression * {
      if (table >= bundle.tables().size() || phase > phases.size())
        return nullptr;
      return phase == 0 ? &bundle.tables()[table].arena
                        : &phases[phase - 1].tables[table].arena;
    };
    switch (premise.kind) {
    case StagedPremise::Kind::Boolean:
    case StagedPremise::Kind::Nonzero:
    case StagedPremise::Kind::AtMostOne: {
      const auto *arena = arenaOf(premise.phase, premise.table);
      bool many = premise.kind == StagedPremise::Kind::AtMostOne;
      if (!arena || premise.outputs.empty() ||
          (!many && premise.outputs.size() != 1) ||
          premise.outputs.size() > BundleLimits::arity ||
          !premise.field.empty() || premise.bound ||
          llvm::any_of(premise.outputs, [&](uint32_t output) {
            return output >= arena->outputs().size();
          }))
        return zkc::error("staged-premise");
      if (auto error = checkScope(premise.scope))
        return error;
      break;
    }
    case StagedPremise::Kind::CharacteristicExceeds:
      if (!installedField(premise.field) || premise.phase || premise.table ||
          !premise.outputs.empty() || premise.bound < 1 ||
          premise.scope.kind != BundleScopeKind::All || premise.scope.first ||
          premise.scope.second)
        return zkc::error("staged-premise");
      break;
    }
  }
  StagedProgram result(bundle.identity().str(), std::move(phases),
                       std::move(global), std::move(premises));
  if (zkc::printJson(result.encode()).size() > BundleLimits::bytes)
    return zkc::error("staged-limit");
  return result;
}

json::Value StagedProgram::encode() const {
  json::Array phases, premises;
  for (const auto &phase : phases_) {
    json::Array tables;
    for (const auto &table : phase.tables) {
      json::Array groups, assertions;
      for (const auto &group : table.groups)
        groups.push_back(json::Array{group.name, group.field, group.width});
      for (const auto &assertion : table.assertions)
        assertions.push_back(
            json::Array{assertion.output, encodeScope(assertion.scope)});
      tables.push_back(json::Array{std::move(groups), table.arena.encode(),
                                   encodeInputs(table.inputs),
                                   std::move(assertions)});
    }
    phases.push_back(json::Array{encodeSlots(phase.challenges),
                                 encodeSlots(phase.claims), std::move(tables)});
  }
  json::Array globalAssertions;
  for (auto position : global_.assertions)
    globalAssertions.push_back(position);
  for (const auto &premise : premises_) {
    switch (premise.kind) {
    case StagedPremise::Kind::Boolean:
    case StagedPremise::Kind::Nonzero:
      premises.push_back(json::Array{
          premise.kind == StagedPremise::Kind::Boolean ? "boolean" : "nonzero",
          premise.phase, premise.table, premise.outputs.front(),
          encodeScope(premise.scope)});
      break;
    case StagedPremise::Kind::AtMostOne: {
      json::Array outputs;
      for (auto output : premise.outputs)
        outputs.push_back(output);
      premises.push_back(json::Array{"at-most-one", premise.phase,
                                     premise.table, std::move(outputs),
                                     encodeScope(premise.scope)});
      break;
    }
    case StagedPremise::Kind::CharacteristicExceeds:
      premises.push_back(
          json::Array{"characteristic-exceeds", premise.field, premise.bound});
      break;
    }
  }
  return json::Array{"zkc.relation-staged/0", relation_, std::move(phases),
                     json::Array{global_.arena.encode(),
                                 encodeInputs(global_.inputs),
                                 std::move(globalAssertions)},
                     std::move(premises)};
}

std::string StagedProgram::identity() const {
  auto bytes = zkc::printJson(encode());
  return toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
}

namespace {
Expected<std::vector<BundleSlot>> readSlots(const json::Value &value) {
  auto *array = value.getAsArray();
  if (!array || array->size() > BundleLimits::slots)
    return zkc::error("staged-schema");
  std::vector<BundleSlot> result;
  for (const auto &item : *array) {
    auto *slot = row(item, 2);
    auto name = slot ? string((*slot)[0]) : std::nullopt;
    auto field = slot ? string((*slot)[1]) : std::nullopt;
    if (!name || !field)
      return zkc::error("staged-schema");
    result.push_back({*name, *field});
  }
  return result;
}
Expected<std::vector<StagedInput>> readInputs(const json::Value &value) {
  auto *array = value.getAsArray();
  if (!array || array->size() > ring::Limits::inputs)
    return zkc::error("staged-schema");
  std::vector<StagedInput> result;
  for (const auto &item : *array) {
    StagedInput input;
    if (auto *in = row(item, 2, "public")) {
      auto index = natural((*in)[1], BundleLimits::publics);
      if (!index)
        return zkc::error("staged-input");
      input.index = *index;
    } else if (auto *in = row(item, 5, "read")) {
      auto phase = natural((*in)[1], BundleLimits::phases);
      auto group = natural((*in)[2], BundleLimits::groups);
      auto offset = signedOffset((*in)[3]);
      auto column = natural((*in)[4], BundleLimits::width);
      if (!phase || !group || !offset || !column)
        return zkc::error("staged-input");
      input = {StagedInput::Kind::Read, uint32_t(*phase), uint32_t(*group),
               *offset, uint32_t(*column)};
    } else if (auto *in = row(item, 3)) {
      auto tag = (*in)[0].getAsString();
      auto phase = natural((*in)[1], BundleLimits::phases);
      auto index = natural((*in)[2], BundleLimits::slots);
      if (!tag || (*tag != "challenge" && *tag != "claim") || !phase || !index)
        return zkc::error("staged-input");
      input = {*tag == "challenge" ? StagedInput::Kind::Challenge
                                   : StagedInput::Kind::Claim,
               uint32_t(*phase), uint32_t(*index), 0, 0};
    } else {
      return zkc::error("staged-input");
    }
    result.push_back(input);
  }
  return result;
}
Expected<std::vector<uint32_t>> readNaturals(const json::Value &value,
                                             size_t limit) {
  auto *array = value.getAsArray();
  if (!array || array->size() > limit)
    return zkc::error("staged-schema");
  std::vector<uint32_t> result;
  for (const auto &item : *array) {
    auto n = natural(item, UINT32_MAX);
    if (!n)
      return zkc::error("staged-schema");
    result.push_back(*n);
  }
  return result;
}
Expected<StagedPremise> readPremise(const json::Value &value) {
  auto *array = value.getAsArray();
  auto tag =
      array && !array->empty() ? (*array)[0].getAsString() : std::nullopt;
  if (!tag)
    return zkc::error("staged-premise");
  StagedPremise premise{StagedPremise::Kind::Boolean, 0, 0, {}, {}, "", 0};
  if (*tag == "characteristic-exceeds" && array->size() == 3) {
    auto field = string((*array)[1]);
    auto bound = (*array)[2].getAsUINT64();
    if (!field || !bound)
      return zkc::error("staged-premise");
    premise.kind = StagedPremise::Kind::CharacteristicExceeds;
    premise.field = *field;
    premise.bound = *bound;
    return premise;
  }
  if (array->size() != 5 ||
      (*tag != "boolean" && *tag != "nonzero" && *tag != "at-most-one"))
    return zkc::error("staged-premise");
  auto phase = natural((*array)[1], BundleLimits::phases);
  auto table = natural((*array)[2], BundleLimits::tables);
  if (!phase || !table)
    return zkc::error("staged-premise");
  premise.phase = *phase;
  premise.table = *table;
  if (*tag == "at-most-one") {
    premise.kind = StagedPremise::Kind::AtMostOne;
    auto outputs = readNaturals((*array)[3], BundleLimits::arity);
    if (!outputs)
      return zkc::error("staged-premise");
    premise.outputs = std::move(*outputs);
  } else {
    premise.kind = *tag == "boolean" ? StagedPremise::Kind::Boolean
                                     : StagedPremise::Kind::Nonzero;
    auto output = natural((*array)[3], UINT32_MAX);
    if (!output)
      return zkc::error("staged-premise");
    premise.outputs = {uint32_t(*output)};
  }
  auto scope = readScope((*array)[4]);
  if (!scope)
    return scope.takeError();
  premise.scope = *scope;
  return premise;
}
} // namespace

Expected<StagedProgram> readStagedProgram(const Bundle &bundle,
                                          const json::Value &value) {
  auto *root = row(value, 5, "zkc.relation-staged/0");
  if (!root)
    return zkc::error("staged-schema");
  auto relation = (*root)[1].getAsString();
  auto *phaseRows = (*root)[2].getAsArray();
  auto *global = row((*root)[3], 3);
  auto *premiseRows = (*root)[4].getAsArray();
  if (!relation || !phaseRows || !global || !premiseRows)
    return zkc::error("staged-schema");
  if (*relation != bundle.identity())
    return zkc::error("bundle-relation");
  if (phaseRows->size() > BundleLimits::phases ||
      premiseRows->size() > BundleLimits::premises)
    return zkc::error("staged-limit");
  std::vector<StagedPhase> phases;
  for (const auto &item : *phaseRows) {
    auto *phase = row(item, 3);
    auto *tables = phase ? (*phase)[2].getAsArray() : nullptr;
    if (!tables || tables->size() > BundleLimits::tables)
      return zkc::error("staged-schema");
    auto challenges = readSlots((*phase)[0]);
    if (!challenges)
      return challenges.takeError();
    auto claims = readSlots((*phase)[1]);
    if (!claims)
      return claims.takeError();
    StagedPhase result{std::move(*challenges), std::move(*claims), {}};
    for (const auto &tableItem : *tables) {
      auto *table = row(tableItem, 4);
      auto *groups = table ? (*table)[0].getAsArray() : nullptr;
      auto *assertions = table ? (*table)[3].getAsArray() : nullptr;
      if (!groups || !assertions || groups->size() > BundleLimits::groups ||
          assertions->size() > BundleLimits::checks)
        return zkc::error("staged-schema");
      auto arena = ring::readExpression((*table)[1]);
      if (!arena)
        return arena.takeError();
      auto inputs = readInputs((*table)[2]);
      if (!inputs)
        return inputs.takeError();
      StagedTable staged{{}, std::move(*arena), std::move(*inputs), {}};
      for (const auto &groupItem : *groups) {
        auto *group = row(groupItem, 3);
        auto name = group ? string((*group)[0]) : std::nullopt;
        auto field = group ? string((*group)[1]) : std::nullopt;
        auto width =
            group ? natural((*group)[2], BundleLimits::width) : std::nullopt;
        if (!name || !field || !width)
          return zkc::error("staged-schema");
        staged.groups.push_back({*name, *field, uint32_t(*width)});
      }
      for (const auto &assertionItem : *assertions) {
        auto *assertion = row(assertionItem, 2);
        auto output =
            assertion ? natural((*assertion)[0], UINT32_MAX) : std::nullopt;
        if (!output)
          return zkc::error("staged-schema");
        auto scope = readScope((*assertion)[1]);
        if (!scope)
          return scope.takeError();
        staged.assertions.push_back({uint32_t(*output), *scope});
      }
      result.tables.push_back(std::move(staged));
    }
    phases.push_back(std::move(result));
  }
  auto globalArena = ring::readExpression((*global)[0]);
  if (!globalArena)
    return globalArena.takeError();
  auto globalInputs = readInputs((*global)[1]);
  if (!globalInputs)
    return globalInputs.takeError();
  auto globalAssertions = readNaturals((*global)[2], BundleLimits::checks);
  if (!globalAssertions)
    return globalAssertions.takeError();
  std::vector<StagedPremise> premises;
  for (const auto &item : *premiseRows) {
    auto premise = readPremise(item);
    if (!premise)
      return premise.takeError();
    premises.push_back(std::move(*premise));
  }
  return StagedProgram::create(bundle, std::move(phases),
                               {std::move(*globalArena),
                                std::move(*globalInputs),
                                std::move(*globalAssertions)},
                               std::move(premises));
}

Expected<StagedAssignment> readStagedAssignment(const Bundle &bundle,
                                                const StagedProgram &program,
                                                const json::Value &value) {
  auto *root = row(value, 3, "zkc.relation-staged-assignment/0");
  auto text = root ? (*root)[1].getAsString() : std::nullopt;
  auto *phases = root ? (*root)[2].getAsArray() : nullptr;
  if (!text || !phases || phases->size() != program.phases().size())
    return zkc::error("staged-data-schema");
  StagedAssignment result;
  result.program = text->str();
  uint64_t budget = BundleLimits::coordinates;
  for (size_t p = 0; p < phases->size(); ++p) {
    const auto &phase = program.phases()[p];
    auto *entry = row((*phases)[p], 3);
    auto *tables = entry ? (*entry)[2].getAsArray() : nullptr;
    if (!tables || tables->size() != bundle.tables().size())
      return zkc::error("staged-data-schema");
    StagedAssignment::Phase data;
    std::vector<std::string> fields;
    for (const auto &slot : phase.challenges)
      fields.push_back(slot.field);
    auto challenges = readValues((*entry)[0], fields);
    if (!challenges)
      return challenges.takeError();
    fields.clear();
    for (const auto &slot : phase.claims)
      fields.push_back(slot.field);
    auto claims = readValues((*entry)[1], fields);
    if (!claims)
      return claims.takeError();
    data.challenges = std::move(*challenges);
    data.claims = std::move(*claims);
    for (size_t t = 0; t < tables->size(); ++t) {
      if ((*tables)[t].kind() == json::Value::Null) {
        data.tables.push_back(std::nullopt);
        continue;
      }
      auto *groups = (*tables)[t].getAsArray();
      const auto &declared = phase.tables[t].groups;
      if (!groups || groups->size() != declared.size())
        return zkc::error("bundle-group-count");
      std::vector<BundleColumns> columns;
      for (size_t g = 0; g < declared.size(); ++g) {
        auto degree = bundleFieldDegree(declared[g].field);
        if (!degree)
          return degree.takeError();
        auto values = readGroupValues((*groups)[g], *degree, budget);
        if (!values)
          return values.takeError();
        columns.push_back(std::move(*values));
      }
      data.tables.push_back(std::move(columns));
    }
    result.phases.push_back(std::move(data));
  }
  return result;
}

json::Value encodeStagedAssignment(const Bundle &bundle,
                                   const StagedProgram &program,
                                   const StagedAssignment &assignment) {
  json::Array phases;
  for (size_t p = 0; p < assignment.phases.size(); ++p) {
    const auto &data = assignment.phases[p];
    json::Array challenges, claims, tables;
    for (const auto &value : data.challenges)
      challenges.push_back(encodeValue(value));
    for (const auto &value : data.claims)
      claims.push_back(encodeValue(value));
    for (size_t t = 0; t < data.tables.size() && t < bundle.tables().size();
         ++t) {
      if (!data.tables[t]) {
        tables.push_back(nullptr);
        continue;
      }
      json::Array groups;
      for (size_t g = 0; g < data.tables[t]->size(); ++g) {
        unsigned degree = 1;
        if (p < program.phases().size() &&
            g < program.phases()[p].tables[t].groups.size()) {
          auto known =
              bundleFieldDegree(program.phases()[p].tables[t].groups[g].field);
          if (known)
            degree = *known;
          else
            consumeError(known.takeError());
        }
        groups.push_back(encodeGroupValues((*data.tables[t])[g], degree));
      }
      tables.push_back(std::move(groups));
    }
    phases.push_back(json::Array{std::move(challenges), std::move(claims),
                                 std::move(tables)});
  }
  return json::Array{"zkc.relation-staged-assignment/0", assignment.program,
                     std::move(phases)};
}

Expected<StagedEvaluation>
StagedProgram::evaluate(const Bundle &bundle, const BundleConfiguration &config,
                        const BundleInstance &instance,
                        const BundleWitness &witness,
                        const StagedAssignment &assignment) const {
  if (bundle.identity() != relation_)
    return zkc::error("bundle-relation");
  Fields fields;
  auto base = admitData(bundle, config, instance, witness, fields, relation_);
  if (!base)
    return base.takeError();
  if (assignment.program != identity())
    return zkc::error("staged-program");
  if (assignment.phases.size() != phases_.size())
    return zkc::error("staged-data-shape");
  auto tables = bundle.tables();
  // Shape, presence and windows before any value is parsed.
  uint64_t coordinates = 0, work = 0;
  for (size_t p = 0; p < phases_.size(); ++p) {
    const auto &phase = phases_[p];
    const auto &data = assignment.phases[p];
    if (data.challenges.size() != phase.challenges.size() ||
        data.claims.size() != phase.claims.size())
      return zkc::error("staged-slot-shape");
    if (data.tables.size() != tables.size())
      return zkc::error("staged-data-shape");
    for (size_t t = 0; t < tables.size(); ++t) {
      const auto &state = base->tables[t];
      const auto &table = phase.tables[t];
      auto context = [&](StringRef code) {
        return zkc::error(code, tables[t].name + "@" + std::to_string(p + 1));
      };
      if (state.present != data.tables[t].has_value())
        return context("staged-presence");
      if (!state.present)
        continue;
      if (data.tables[t]->size() != table.groups.size())
        return context("bundle-group-count");
      for (size_t g = 0; g < table.groups.size(); ++g) {
        auto degree = bundleFieldDegree(table.groups[g].field);
        if (!degree)
          return degree.takeError();
        if ((*data.tables[t])[g].size() !=
            uint64_t(state.height) * table.groups[g].width * *degree)
          return context("bundle-group-shape");
        coordinates += (*data.tables[t])[g].size();
        if (coordinates > BundleLimits::coordinates)
          return context("bundle-data-limit");
      }
      for (const auto &assertion : table.assertions)
        if (auto error = windowAt(
                assertion.scope, tables[t].readModel, state.height,
                stagedOffsets(table.arena, table.inputs, assertion.output)))
          return withDetail(std::move(error), tables[t].name);
      if (!table.assertions.empty())
        work += uint64_t(state.height) *
                (table.arena.nodes().size() + table.arena.inputs().size() +
                 table.assertions.size() + 1);
      if (work > BundleLimits::work)
        return context("bundle-work-limit");
    }
  }
  // Parse challenges, claims and staged groups.
  std::vector<std::vector<Scalar>> challenges(phases_.size()),
      claims(phases_.size());
  std::vector<std::vector<std::vector<std::vector<APInt>>>> groups(
      phases_.size());
  for (size_t p = 0; p < phases_.size(); ++p) {
    const auto &phase = phases_[p];
    const auto &data = assignment.phases[p];
    for (auto [slots, values, out] :
         {std::make_tuple(&phase.challenges, &data.challenges, &challenges[p]),
          std::make_tuple(&phase.claims, &data.claims, &claims[p])})
      for (size_t i = 0; i < slots->size(); ++i) {
        auto arithmetic = fields.get((*slots)[i].field);
        if (!arithmetic)
          return arithmetic.takeError();
        auto value = (*arithmetic)->parse((*values)[i]);
        if (!value)
          return withDetail(value.takeError(), (*slots)[i].name);
        out->push_back(std::move(*value));
      }
    groups[p].resize(tables.size());
    for (size_t t = 0; t < tables.size(); ++t) {
      if (!data.tables[t])
        continue;
      for (size_t g = 0; g < phase.tables[t].groups.size(); ++g) {
        const auto &group = phase.tables[t].groups[g];
        auto arithmetic = fields.get(group.field);
        if (!arithmetic)
          return arithmetic.takeError();
        std::vector<APInt> parsed;
        if (auto error =
                checkColumns((*data.tables[t])[g],
                             uint64_t(base->tables[t].height) * group.width,
                             **arithmetic, parsed))
          return withDetail(std::move(error), group.name);
        groups[p][t].push_back(std::move(parsed));
      }
    }
  }
  StagedEvaluation result;
  result.work = work;
  std::map<std::pair<std::string, std::string>, Scalar> constants;
  auto scalarInput = [&](const StagedInput &input) -> Scalar {
    switch (input.kind) {
    case StagedInput::Kind::Public:
      return base->publics[input.index];
    case StagedInput::Kind::Challenge:
      return challenges[input.phase - 1][input.index];
    case StagedInput::Kind::Claim:
      return claims[input.phase - 1][input.index];
    case StagedInput::Kind::Read:
      break;
    }
    llvm_unreachable("scalar staged input");
  };
  for (uint32_t p = 0; p < phases_.size(); ++p) {
    for (uint32_t t = 0; t < tables.size(); ++t) {
      const auto &state = base->tables[t];
      const auto &table = phases_[p].tables[t];
      if (!state.present || table.assertions.empty())
        continue;
      for (uint32_t a = 0; a < table.assertions.size(); ++a) {
        const auto &assertion = table.assertions[a];
        auto [lo, hi] = scopeRows(assertion.scope, state.height);
        auto field =
            table.arena.facts()[table.arena.outputs()[assertion.output]].field;
        auto arithmetic = fields.get(field);
        if (!arithmetic)
          return arithmetic.takeError();
        for (uint32_t r = lo; r < hi; ++r) {
          auto fetch = [&](uint32_t index) -> Expected<Scalar> {
            const auto &input = table.inputs[index];
            if (input.kind != StagedInput::Kind::Read)
              return scalarInput(input);
            const auto &group =
                input.phase == 0
                    ? StagedGroup{tables[t].groups[input.index].field,
                                  tables[t].groups[input.index].field,
                                  tables[t].groups[input.index].width}
                    : phases_[input.phase - 1].tables[t].groups[input.index];
            auto degree = bundleFieldDegree(group.field);
            if (!degree)
              return degree.takeError();
            const auto &coordinates =
                input.phase == 0 ? state.groups[input.index]
                                 : groups[input.phase - 1][t][input.index];
            return element(
                coordinates, *degree, group.width,
                readRow(tables[t].readModel, state.height, r, input.offset),
                input.column);
          };
          RowAlgebra algebra{fields, fetch, constants};
          auto values =
              table.arena.evaluate<Scalar>({assertion.output}, algebra);
          if (!values)
            return values.takeError();
          result.satisfied &= (*arithmetic)->isZero(values->front());
          result.residuals.push_back(
              {p + 1, t, a, r, (*arithmetic)->print(values->front())});
        }
      }
    }
  }
  if (!global_.assertions.empty()) {
    auto fetch = [&](uint32_t index) -> Expected<Scalar> {
      return scalarInput(global_.inputs[index]);
    };
    RowAlgebra algebra{fields, fetch, constants};
    auto values = global_.arena.evaluate<Scalar>(global_.assertions, algebra);
    if (!values)
      return values.takeError();
    for (size_t i = 0; i < global_.assertions.size(); ++i) {
      auto field =
          global_.arena.facts()[global_.arena.outputs()[global_.assertions[i]]]
              .field;
      auto arithmetic = fields.get(field);
      if (!arithmetic)
        return arithmetic.takeError();
      result.satisfied &= (*arithmetic)->isZero((*values)[i]);
      result.global.push_back((*arithmetic)->print((*values)[i]));
    }
  }
  return result;
}

json::Value StagedEvaluation::encode() const {
  json::Array residualRows, globalRows;
  for (const auto &r : residuals)
    residualRows.push_back(json::Array{r.phase, r.table, r.assertion, r.row,
                                       encodeValue(r.value)});
  for (const auto &value : global)
    globalRows.push_back(encodeValue(value));
  return json::Object{{"satisfied", satisfied},
                      {"work", work},
                      {"residuals", std::move(residualRows)},
                      {"global", std::move(globalRows)}};
}

} // namespace zkc::relation
