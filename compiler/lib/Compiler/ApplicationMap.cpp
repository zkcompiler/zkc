#include "zkc/Compiler/ApplicationMap.h"
#include "ApplicationMapData.h"
#include "llvm/ADT/STLExtras.h"
#include <optional>

using namespace llvm;
namespace zkc::protocol {
namespace {
using namespace application_map;
class Producer {
  const View &source, &candidate;
  Budget &budget;
  json::Array applications, instructions;
  size_t remainingBytes = byteLimit;

  Error append(json::Array &table, json::Value row) {
    // Account for each complete row before retaining it. Empty application
    // bodies can expand without adding candidate instructions, so the input
    // export's byte bound alone does not bound the proposed forest's storage.
    size_t bytes = printJson(row).size() + !table.empty();
    if (bytes > remainingBytes)
      return error("application-map-limit");
    remainingBytes -= bytes;
    table.push_back(std::move(row));
    return Error::success();
  }

  Expected<unsigned> application(const Definition &definition,
                                 std::optional<unsigned> parent,
                                 const Definition &caller, const Path &path,
                                 const ValueContext &context,
                                 const Instruction *call) {
    if (applications.size() == rowLimit ||
        !budget.charge(24 + path.size() + definition.roles.size() * 4))
      return error("application-map-limit");
    unsigned id = applications.size();
    json::Array roles, inputs, outputs;
    for (unsigned i = 0; i < definition.roles.size(); ++i) {
      unsigned actual = i;
      if (call) {
        auto name = (*(*call->descriptor.getAsArray())[2].getAsArray())[i]
                        .getAsString();
        auto found = llvm::find(caller.roles, name->str());
        if (found == caller.roles.end())
          return error("application-map-carrier");
        actual = found - caller.roles.begin();
      }
      roles.push_back(json::Array{std::to_string(i), std::to_string(actual)});
    }
    for (unsigned i = 0; i < definition.body.inputs.size(); ++i) {
      auto value = call ? context.at(call->operands.at(i))
                        : Value{definition.name, {}, true, 0, i};
      if (!budget.charge(20 + value.region.size()))
        return error("application-map-limit");
      inputs.push_back(json::Array{std::to_string(i), encodeValue(value)});
    }
    if (call) {
      if (!budget.charge(call->results.size() * (20 + path.size())))
        return error("application-map-limit");
      for (unsigned i = 0; i < call->results.size(); ++i)
        outputs.push_back(json::Array{
            std::to_string(i),
            encodeValue({caller.name, Path(path.begin(), path.end() - 1), false,
                         path.back(), i})});
    } else {
      auto returned =
          arguments(definition.name, {}, definition.body.inputs.size());
      for (auto [i, instruction] : enumerate(definition.body.instructions)) {
        if (!budget.charge(1 + instruction.results.size()))
          return error("application-map-limit");
        prependResults(returned, definition.name, {}, i,
                       instruction.results.size());
      }
      for (auto [i, index] : enumerate(definition.body.returned)) {
        if (index >= returned.size())
          return error("application-map-carrier");
        if (!budget.charge(20 + returned[index].region.size()))
          return error("application-map-limit");
        outputs.push_back(
            json::Array{std::to_string(i), encodeValue(returned[index])});
      }
    }
    if (auto e =
            append(applications,
                   json::Object{
                       {"id", std::to_string(id)},
                       {"parent", parent ? json::Value(std::to_string(*parent))
                                         : json::Value(nullptr)},
                       {"source_definition", caller.name},
                       {"source_path", encodePath(path)},
                       {"callee", definition.name},
                       {"roles", std::move(roles)},
                       {"arguments", std::move(inputs)},
                       {"results", std::move(outputs)},
                       {"written", nullptr}}))
      return std::move(e);
    return id;
  }
  Error row(StringRef target, const Path &targetPath,
            std::optional<unsigned> app, StringRef original,
            const Path &sourcePath, bool auxiliary = false) {
    if (targetPath.size() > 64 || sourcePath.size() > 64 ||
        instructions.size() == rowLimit ||
        !budget.charge(16 + targetPath.size() + sourcePath.size()))
      return error("application-map-limit");
    return append(
        instructions,
        json::Object{{"target_definition", target.str()},
                     {"target_path", encodePath(targetPath)},
                     {"application", app ? json::Value(std::to_string(*app))
                                         : json::Value(nullptr)},
                     {"source_definition", original.str()},
                     {"source_path", auxiliary
                                         ? json::Value(nullptr)
                                         : json::Value(encodePath(sourcePath))},
                     {"purpose", auxiliary ? "auxiliary" : "source"}});
  }
  Error body(const Definition &definition, const Block &original,
             const Path &sourceRegion, const Definition &targetDefinition,
             const Block &actual, const Path &targetRegion, unsigned &cursor,
             std::optional<unsigned> app, bool inlineBody, bool expandHelpers,
             unsigned depth) {
    if (depth > 64 || sourceRegion.size() > 62 || targetRegion.size() > 62 ||
        !budget.charge(1 + original.inputs.size()))
      return error("application-map-limit");
    auto context =
        arguments(definition.name, sourceRegion, original.inputs.size());
    for (auto [i, instruction] : enumerate(original.instructions)) {
      if (!budget.charge(instruction.operands.size() +
                         instruction.results.size() + 1))
        return error("application-map-limit");
      Path sourcePath = instructionPath(sourceRegion, i);
      bool expand = opcode(instruction) == "protocol_apply";
      if (opcode(instruction) == "call" && expandHelpers) {
        // A retained helper call stays a direct association. An expanded
        // helper is role-free and has its own occurrence, even if empty.
        expand = cursor == actual.instructions.size() ||
                 !equalNaturalJson(instruction.descriptor,
                                   actual.instructions[cursor].descriptor);
      }
      if (expand) {
        const auto *calleeDefinition = source.find(callee(instruction));
        if (!calleeDefinition || !calleeDefinition->hasBody || !app)
          return error("application-map-unsupported");
        auto nested = application(*calleeDefinition, app, definition,
                                  sourcePath, context, &instruction);
        if (!nested)
          return nested.takeError();
        auto restrictPorts = [&](const std::vector<bool> &ports) -> Error {
          for (bool restrict : ports) {
            if (!restrict)
              continue;
            if (cursor == actual.instructions.size() ||
                opcode(actual.instructions[cursor]) != "restrict")
              return error("application-map-unsupported",
                           "missing port restriction");
            if (auto e = row(targetDefinition.name,
                             instructionPath(targetRegion, cursor++), *nested,
                             calleeDefinition->name, {}, true))
              return e;
          }
          return Error::success();
        };
        if (auto e = restrictPorts(calleeDefinition->restrictInputs))
          return e;
        if (auto e = body(*calleeDefinition, calleeDefinition->body, {},
                          targetDefinition, actual, targetRegion, cursor,
                          *nested, true, expandHelpers, depth + 1))
          return e;
        if (auto e = restrictPorts(calleeDefinition->restrictOutputs))
          return e;
      } else {
        if (cursor >= actual.instructions.size())
          return error("application-map-unsupported", "instruction shape");
        unsigned targetIndex = cursor++;
        const auto &target = actual.instructions[targetIndex];
        if (auto e = row(targetDefinition.name,
                         instructionPath(targetRegion, targetIndex), app,
                         definition.name, sourcePath))
          return e;
        if (instruction.regions.size() != target.regions.size())
          return error("application-map-unsupported", "region shape");
        for (unsigned r = 0; r < instruction.regions.size(); ++r) {
          unsigned inner = 0;
          if (auto e = body(definition, instruction.regions[r],
                            regionPath(sourceRegion, i, r), targetDefinition,
                            target.regions[r],
                            regionPath(targetRegion, targetIndex, r), inner,
                            app, false, expandHelpers, depth + 1))
            return e;
        }
      }
      prependResults(context, definition.name, sourceRegion, i,
                     instruction.results.size());
    }
    if (inlineBody)
      return Error::success();
    if (cursor != actual.instructions.size())
      return error("application-map-unsupported",
                   "extra candidate instruction");
    return row(targetDefinition.name, instructionPath(targetRegion, cursor),
               app, definition.name,
               instructionPath(sourceRegion, original.instructions.size()));
  }

public:
  Producer(const View &source, const View &candidate, Budget &budget)
      : source(source), candidate(candidate), budget(budget) {}
  Expected<json::Value> run() {
    const auto &a = *source.wire.getAsArray();
    const auto &b = *candidate.wire.getAsArray();
    json::Value record = json::Object{
        {"format", "zkc.application-map/0"},
        {"source",
         json::Object{{"format", a[0]}, {"digest", a[2]}, {"entry", a[3]}}},
        {"candidate", json::Object{{"format", b[0]}, {"digest", b[2]}}},
        {"applications", json::Array{}},
        {"instructions", json::Array{}}};
    size_t framing = printJson(record).size() + 1;
    if (framing > remainingBytes)
      return error("application-map-limit");
    remainingBytes -= framing;
    // Domain constructors have a separate logical row grammar and are retained
    // exactly. Their instruction-count ordinal addresses the domain yield.
    for (const auto &value : *(*source.wire.getAsArray())[4].getAsArray()) {
      const auto &domain = *value.getAsArray();
      auto name = *domain[1].getAsString();
      for (unsigned i = 0; i <= domain[3].getAsArray()->size(); ++i)
        if (auto e = row(name, {i}, std::nullopt, name, {i}))
          return std::move(e);
    }
    for (unsigned i = 0; i < source.definitions.size(); ++i) {
      const auto &definition = source.definitions[i];
      if (!definition.hasBody)
        continue;
      std::optional<unsigned> root;
      if (definition.kind == "protocol") {
        auto id = application(definition, {}, definition, {}, {}, nullptr);
        if (!id)
          return id.takeError();
        root = *id;
      }
      unsigned cursor = 0;
      if (auto e = body(definition, definition.body, {},
                        candidate.definitions[i], candidate.definitions[i].body,
                        {}, cursor, root, false, root.has_value(), 0))
        return std::move(e);
    }
    (*record.getAsObject())["applications"] = std::move(applications);
    (*record.getAsObject())["instructions"] = std::move(instructions);
    return record;
  }
};
} // namespace

Expected<std::string> produceApplicationMap(StringRef originalBytes,
                                            StringRef candidateBytes,
                                            StringRef entry,
                                            mlir::MLIRContext &context) {
  application_map::Budget budget;
  auto source = application_map::readView(originalBytes, entry, context, budget,
                                          StructuredSourceProfile::Original);
  if (!source)
    return source.takeError();
  auto candidate =
      application_map::readView(candidateBytes, entry, context, budget,
                                StructuredSourceProfile::Prepared);
  if (!candidate)
    return candidate.takeError();
  if (auto e = application_map::compareInventory(*source, *candidate))
    return std::move(e);
  auto record = Producer(*source, *candidate, budget).run();
  if (!record)
    return record.takeError();
  if (auto e = application_map::chargeTree(*record, budget))
    return std::move(e);
  if (auto e =
          application_map::checkRecord(*source, *candidate, *record, budget))
    return std::move(e);
  auto bytes = printJson(*record) + '\n';
  // Check the published lexical limits too, before returning any proposal.
  auto bounded = application_map::parseRecord(bytes);
  if (!bounded)
    return bounded.takeError();
  return bytes;
}
} // namespace zkc::protocol
