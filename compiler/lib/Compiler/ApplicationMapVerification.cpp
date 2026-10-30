#include "ApplicationMapData.h"
#include "zkc/Compiler/ApplicationMap.h"
#include "zkc/Dialect/Mathematical.h"
#include "llvm/ADT/STLExtras.h"
#include <optional>

using namespace llvm;
namespace zkc::protocol::application_map {
namespace {
using Terms = std::deque<unsigned>;
using Roles = std::map<std::string, std::string>;
bool shape(const json::Object *object,
           std::initializer_list<StringRef> fields) {
  return object && object->size() == fields.size() &&
         all_of(fields, [&](StringRef field) { return object->get(field); });
}
bool same(const json::Value *actual, const json::Value &expected) {
  return actual && equalNaturalJson(*actual, expected);
}
json::Value ordinal(std::optional<unsigned> number) {
  return number ? json::Value(std::to_string(*number)) : json::Value(nullptr);
}
bool treeField(const json::Object &object, StringRef field,
               const json::Value &expected) {
  return same(object.get(field), expected);
}
bool sameTypes(ArrayRef<json::Value> a, ArrayRef<json::Value> b) {
  return a.size() == b.size() &&
         std::equal(a.begin(), a.end(), b.begin(), equalNaturalJson);
}
class Checker {
  View &source, &candidate;
  const json::Array &applications, &instructions;
  Budget &budget;
  unsigned nextApplication = 0, nextInstruction = 0, nextTerm = 1;

  Error mismatch(StringRef detail) {
    return error("application-map-correspondence", detail);
  }
  Expected<Terms> select(const Terms &context, ArrayRef<unsigned> indices) {
    if (!budget.charge(indices.size()))
      return error("application-map-limit");
    Terms result;
    for (unsigned index : indices) {
      if (index >= context.size())
        return error("application-map-carrier", "operand context");
      result.push_back(context[index]);
    }
    return result;
  }
  Terms fresh(unsigned count) {
    Terms result;
    for (unsigned i = 0; i < count; ++i)
      result.push_back(nextTerm++);
    return result;
  }
  static void prepend(Terms &context, const Terms &results) {
    context.insert(context.begin(), results.begin(), results.end());
  }
  std::string role(StringRef name, const Roles &roles) {
    auto found = roles.find(name.str());
    return found == roles.end() ? name.str() : found->second;
  }
  json::Value mappedDescriptor(const Instruction &instruction,
                               const Roles &roles) {
    auto result = instruction.descriptor;
    auto &row = *result.getAsArray();
    auto one = [&](json::Value &value) {
      if (auto name = value.getAsString())
        value = role(*name, roles);
    };
    auto set = [&](json::Value &value) {
      for (auto &name : *value.getAsArray())
        one(name);
    };
    auto code = opcode(instruction);
    if (code == "protocol_repeat") {
      set(row[3]);
      for (auto &scope : *row[4].getAsArray())
        set(scope);
    } else if (code == "exchange") {
      one(row[1]);
      one(row[2]);
    } else if (code == "draw" || code == "guard" || code == "oracle_query" ||
               code == "oracle_contents")
      one(row[1]);
    else if (code == "local_call")
      one(row[2]);
    else if (code == "assemble" || code == "restrict")
      set(row[1]);
    else if (code == "oracle_send" || code == "oracle_input" ||
             code == "oracle_components") {
      one(row[1]);
      set(row[2]);
    } else if (code == "oracle_virtual") {
      one(row[2]);
      set(row[3]);
    } else if (code == "oracle_sequence_append" || code == "oracle_sequence_at")
      set(row[3]);
    return result;
  }
  Error instruction(StringRef target, const Path &targetPath,
                    std::optional<unsigned> application, StringRef original,
                    const Path &sourcePath, bool auxiliary = false) {
    if (targetPath.size() > 64 || sourcePath.size() > 64 ||
        !budget.charge(1 + targetPath.size() + sourcePath.size()))
      return error("application-map-limit");
    if (nextInstruction >= instructions.size())
      return mismatch("missing instruction or terminator");
    const auto *row = instructions[nextInstruction++].getAsObject();
    if (!shape(row, {"target_definition", "target_path", "application",
                     "source_definition", "source_path", "purpose"}) ||
        row->getString("target_definition") != target ||
        !treeField(*row, "target_path", encodePath(targetPath)) ||
        !treeField(*row, "application", ordinal(application)) ||
        row->getString("source_definition") != original ||
        !treeField(*row, "source_path",
                   auxiliary ? json::Value(nullptr)
                             : json::Value(encodePath(sourcePath))) ||
        row->getString("purpose") != (auxiliary ? "auxiliary" : "source"))
      return mismatch("instruction association");
    return Error::success();
  }
  Error portValues(const json::Value *value, ArrayRef<Value> expected) {
    const auto *ports = value ? value->getAsArray() : nullptr;
    if (!ports || ports->size() != expected.size())
      return mismatch("logical port count");
    for (unsigned i = 0; i < expected.size(); ++i) {
      if (!budget.charge(1 + expected[i].region.size()))
        return error("application-map-limit");
      const auto *pair = (*ports)[i].getAsArray();
      // Exact equality includes the producer discriminator, every lexical
      // ordinal, components and unknown fields. Equal types never stand in
      // for the source's actual operand producer.
      if (!pair || pair->size() != 2 ||
          (*pair)[0].getAsString() != std::to_string(i) ||
          !equalNaturalJson((*pair)[1], encodeValue(expected[i])))
        return mismatch("logical port producer");
    }
    return Error::success();
  }
  Expected<unsigned> application(const Definition &definition,
                                 std::optional<unsigned> parent,
                                 const Definition &caller, const Path &path,
                                 const ValueContext &sourceValues,
                                 const Instruction *call) {
    if (!budget.charge() || path.size() > 64)
      return error("application-map-limit");
    if (nextApplication >= applications.size())
      return mismatch("missing materialized application");
    unsigned id = nextApplication++;
    const auto *row = applications[id].getAsObject();
    if (!shape(row, {"id", "parent", "source_definition", "source_path",
                     "callee", "roles", "arguments", "results", "written"}) ||
        row->getString("id") != std::to_string(id) ||
        !treeField(*row, "parent", ordinal(parent)) ||
        row->getString("source_definition") != caller.name ||
        !treeField(*row, "source_path", encodePath(path)) ||
        row->getString("callee") != definition.name ||
        !treeField(*row, "written", nullptr))
      return mismatch("application identity, parent, path or written link");
    const auto *roles = row->getArray("roles");
    if (!roles || roles->size() != definition.roles.size())
      return mismatch("role roster");
    for (unsigned r = 0; r < definition.roles.size(); ++r) {
      unsigned callerRole = r;
      if (call) {
        auto actual = (*(*call->descriptor.getAsArray())[2].getAsArray())[r]
                          .getAsString();
        auto found = llvm::find(caller.roles, actual->str());
        if (found == caller.roles.end())
          return mismatch("source application role");
        callerRole = found - caller.roles.begin();
      }
      const auto *pair = (*roles)[r].getAsArray();
      if (!pair || pair->size() != 2 ||
          (*pair)[0].getAsString() != std::to_string(r) ||
          (*pair)[1].getAsString() != std::to_string(callerRole))
        return mismatch("role substitution");
    }
    std::vector<Value> arguments, results;
    if (call) {
      if (call->operands.size() != definition.body.inputs.size() ||
          call->results.size() != definition.body.outputs.size() ||
          path.empty())
        return mismatch("source application signature");
      for (unsigned operand : call->operands) {
        if (operand >= sourceValues.size())
          return mismatch("source operand producer");
        arguments.push_back(sourceValues[operand]);
      }
      Path lexical(path.begin(), path.end() - 1);
      for (unsigned r = 0; r < call->results.size(); ++r)
        results.push_back({caller.name, lexical, false, path.back(), r});
    } else {
      auto values = application_map::arguments(definition.name, {},
                                               definition.body.inputs.size());
      arguments.assign(values.begin(), values.end());
      for (auto [i, op] : enumerate(definition.body.instructions)) {
        if (!budget.charge(1 + op.results.size()))
          return error("application-map-limit");
        prependResults(values, definition.name, {}, i, op.results.size());
      }
      for (unsigned returned : definition.body.returned) {
        if (returned >= values.size())
          return mismatch("root return producer");
        results.push_back(values[returned]);
      }
    }
    if (auto e = portValues(row->get("arguments"), arguments))
      return std::move(e);
    if (auto e = portValues(row->get("results"), results))
      return std::move(e);
    return id;
  }
  bool helperExpanded(unsigned parent, const Definition &definition,
                      const Path &path) {
    if (nextApplication == applications.size())
      return false;
    const auto *next = applications[nextApplication].getAsObject();
    return next && treeField(*next, "parent", ordinal(parent)) &&
           next->getString("source_definition") == definition.name &&
           treeField(*next, "source_path", encodePath(path));
  }
  Expected<unsigned> restriction(const Definition &targetDefinition,
                                 const Block &target, const Path &region,
                                 unsigned &cursor, Terms &targetValues,
                                 unsigned app, const Definition &definition,
                                 unsigned input, const json::Value &type,
                                 const std::vector<std::string> &owners,
                                 const Roles &roles) {
    if (cursor >= target.instructions.size())
      return mismatch("missing port restriction");
    unsigned index = cursor++;
    const auto &actual = target.instructions[index];
    json::Array scope;
    for (const auto &owner : owners)
      scope.push_back(role(owner, roles));
    json::Value descriptor = json::Array{"restrict", std::move(scope)};
    if (!equalNaturalJson(actual.descriptor, descriptor) ||
        actual.operands.size() != 1 || actual.results.size() != 1 ||
        !equalNaturalJson(actual.results[0], type) || !actual.regions.empty() ||
        !actual.site.empty())
      return mismatch("port restriction rule");
    auto operands = select(targetValues, actual.operands);
    if (!operands)
      return operands.takeError();
    if (operands->front() != input)
      return mismatch("port restriction SSA producer");
    if (auto e =
            instruction(targetDefinition.name, instructionPath(region, index),
                        app, definition.name, {}, true))
      return std::move(e);
    unsigned result = nextTerm++;
    targetValues.push_front(result);
    return result;
  }
  Expected<Terms> block(const Definition &definition, const Block &original,
                        const Path &sourceRegion,
                        const Definition &targetDefinition, const Block &target,
                        const Path &targetRegion, unsigned &cursor,
                        std::optional<unsigned> app, Terms values,
                        Terms &targetValues, const Roles &roles,
                        StringRef prefix, bool inlined, unsigned depth) {
    if (depth > 64 || sourceRegion.size() > 62 || targetRegion.size() > 62 ||
        !budget.charge())
      return error("application-map-limit");
    for (const auto &type : original.inputs)
      if (auto e = chargeTree(type, budget))
        return std::move(e);
    for (const auto &type : original.outputs)
      if (auto e = chargeTree(type, budget))
        return std::move(e);
    ValueContext sourceValues =
        arguments(definition.name, sourceRegion, original.inputs.size());
    for (auto [i, op] : enumerate(original.instructions)) {
      if (!budget.charge(1 + op.results.size()))
        return error("application-map-limit");
      if (auto e = chargeTree(op.descriptor, budget))
        return std::move(e);
      for (const auto &type : op.results)
        if (auto e = chargeTree(type, budget))
          return std::move(e);
      auto inputs = select(values, op.operands);
      if (!inputs)
        return inputs.takeError();
      auto sourcePath = instructionPath(sourceRegion, i);
      bool expand = opcode(op) == "protocol_apply" ||
                    (opcode(op) == "call" && app &&
                     helperExpanded(*app, definition, sourcePath));
      Terms results;
      if (expand) {
        const auto *calleeDefinition = source.find(callee(op));
        if (!app || !calleeDefinition || !calleeDefinition->hasBody ||
            (calleeDefinition->kind != "protocol" &&
             calleeDefinition->kind != "math"))
          return mismatch("expanded source call");
        auto nested = application(*calleeDefinition, app, definition,
                                  sourcePath, sourceValues, &op);
        if (!nested)
          return nested.takeError();
        Roles substitution;
        for (unsigned r = 0; r < calleeDefinition->roles.size(); ++r) {
          auto name =
              (*(*op.descriptor.getAsArray())[2].getAsArray())[r].getAsString();
          substitution[calleeDefinition->roles[r]] = role(*name, roles);
        }
        for (unsigned p = 0; p < calleeDefinition->restrictInputs.size(); ++p)
          if (calleeDefinition->restrictInputs[p]) {
            auto restricted =
                restriction(targetDefinition, target, targetRegion, cursor,
                            targetValues, *nested, *calleeDefinition,
                            (*inputs)[p], calleeDefinition->body.inputs[p],
                            calleeDefinition->inputRoles[p], substitution);
            if (!restricted)
              return restricted.takeError();
            (*inputs)[p] = *restricted;
          }
        std::string nestedPrefix = prefix.str();
        if (calleeDefinition->kind == "protocol")
          nestedPrefix =
              prefix.empty()
                  ? op.site
                  : mathematical::expandedApplicationSite(prefix, op.site);
        if (nestedPrefix.size() > 4096)
          return error("application-map-limit");
        auto returned = block(*calleeDefinition, calleeDefinition->body, {},
                              targetDefinition, target, targetRegion, cursor,
                              *nested, std::move(*inputs), targetValues,
                              substitution, nestedPrefix, true, depth + 1);
        if (!returned)
          return returned.takeError();
        results = std::move(*returned);
        for (unsigned p = 0; p < calleeDefinition->restrictOutputs.size(); ++p)
          if (calleeDefinition->restrictOutputs[p]) {
            auto restricted =
                restriction(targetDefinition, target, targetRegion, cursor,
                            targetValues, *nested, *calleeDefinition,
                            results[p], calleeDefinition->body.outputs[p],
                            calleeDefinition->outputRoles[p], substitution);
            if (!restricted)
              return restricted.takeError();
            results[p] = *restricted;
          }
      } else {
        if (cursor >= target.instructions.size())
          return mismatch("missing actual candidate instruction");
        unsigned index = cursor++;
        const auto &actual = target.instructions[index];
        auto actualInputs = select(targetValues, actual.operands);
        if (!actualInputs)
          return actualInputs.takeError();
        auto site =
            prefix.empty() || op.site.empty()
                ? op.site
                : mathematical::expandedApplicationSite(prefix, op.site);
        if (!equalNaturalJson(mappedDescriptor(op, roles), actual.descriptor) ||
            !sameTypes(op.results, actual.results) ||
            *inputs != *actualInputs || site != actual.site ||
            op.regions.size() != actual.regions.size())
          return mismatch(
              "actual instruction, type, role, site or SSA operand");
        if (auto e = instruction(targetDefinition.name,
                                 instructionPath(targetRegion, index), app,
                                 definition.name, sourcePath))
          return std::move(e);
        for (unsigned r = 0; r < op.regions.size(); ++r) {
          const auto &a = op.regions[r];
          const auto &b = actual.regions[r];
          if (!sameTypes(a.inputs, b.inputs) ||
              !sameTypes(a.outputs, b.outputs))
            return mismatch("closed region logical ports");
          auto innerValues = fresh(a.inputs.size());
          auto innerActual = innerValues;
          unsigned innerCursor = 0;
          auto checked =
              block(definition, a, regionPath(sourceRegion, i, r),
                    targetDefinition, b, regionPath(targetRegion, index, r),
                    innerCursor, app, std::move(innerValues), innerActual,
                    roles, prefix, false, depth + 1);
          if (!checked)
            return checked.takeError();
        }
        results = fresh(op.results.size());
        prepend(targetValues, results);
      }
      if (results.size() != op.results.size())
        return mismatch("expanded result arity");
      prepend(values, results);
      prependResults(sourceValues, definition.name, sourceRegion, i,
                     op.results.size());
    }
    auto returned = select(values, original.returned);
    if (!returned)
      return returned.takeError();
    if (inlined) {
      if ((*original.terminator.getAsArray())[0].getAsString() != "return")
        return mismatch("expanded body lacks structured outer return");
      return returned;
    }
    if (cursor != target.instructions.size())
      return mismatch("unaccounted actual candidate instruction");
    auto expectedTerminal = *original.terminator.getAsArray();
    auto actualTerminal = *target.terminator.getAsArray();
    bool stop = expectedTerminal[0].getAsString() == "stop";
    if (!stop) {
      auto actualReturned = select(targetValues, target.returned);
      if (!actualReturned)
        return actualReturned.takeError();
      if (*returned != *actualReturned)
        return mismatch("actual terminator SSA producer");
      expectedTerminal[1] = nullptr;
      actualTerminal[1] = nullptr;
    }
    if (!equalNaturalJson(json::Value(std::move(expectedTerminal)),
                          json::Value(std::move(actualTerminal))))
      return mismatch("actual terminator");
    if (auto e = instruction(
            targetDefinition.name, instructionPath(targetRegion, cursor), app,
            definition.name,
            instructionPath(sourceRegion, original.instructions.size())))
      return std::move(e);
    return returned;
  }

public:
  Checker(View &source, View &candidate, const json::Array &applications,
          const json::Array &instructions, Budget &budget)
      : source(source), candidate(candidate), applications(applications),
        instructions(instructions), budget(budget) {}
  Error run() {
    // Enumerate the actual candidate inventory, including every domain
    // constructor and every terminal row. Inventory equality was checked first.
    for (const auto &value : *(*candidate.wire.getAsArray())[4].getAsArray()) {
      const auto &domain = *value.getAsArray();
      auto name = *domain[1].getAsString();
      for (unsigned i = 0; i <= domain[3].getAsArray()->size(); ++i)
        if (auto e = instruction(name, {i}, {}, name, {i}))
          return e;
    }
    for (unsigned d = 0; d < candidate.definitions.size(); ++d) {
      const auto &actual = candidate.definitions[d];
      const auto &original = source.definitions[d];
      if (!actual.hasBody)
        continue;
      std::optional<unsigned> root;
      Roles roles;
      if (actual.kind == "protocol") {
        auto checked = application(original, {}, original, {}, {}, nullptr);
        if (!checked)
          return checked.takeError();
        root = *checked;
        for (const auto &name : original.roles)
          roles[name] = name;
      }
      Terms values = fresh(actual.body.inputs.size());
      Terms targetValues = values;
      unsigned cursor = 0;
      auto checked =
          block(original, original.body, {}, actual, actual.body, {}, cursor,
                root, std::move(values), targetValues, roles, "", false, 0);
      if (!checked)
        return checked.takeError();
    }
    if (nextApplication != applications.size() ||
        nextInstruction != instructions.size())
      return mismatch("extraneous application or duplicate coverage");
    return Error::success();
  }
};
} // namespace

Error checkRecord(View &source, View &candidate, const json::Value &record,
                  Budget &budget) {
  const auto *root = record.getAsObject();
  if (!shape(root, {"format", "source", "candidate", "applications",
                    "instructions"}) ||
      root->getString("format") != "zkc.application-map/0")
    return error("application-map-schema");
  const auto *sourceIdentity = root->getObject("source");
  const auto *candidateIdentity = root->getObject("candidate");
  const auto &a = *source.wire.getAsArray();
  const auto &b = *candidate.wire.getAsArray();
  if (!shape(sourceIdentity, {"format", "digest", "entry"}) ||
      !shape(candidateIdentity, {"format", "digest"}) ||
      !same(sourceIdentity->get("format"), a[0]) ||
      !same(sourceIdentity->get("digest"), a[2]) ||
      !same(sourceIdentity->get("entry"), a[3]) ||
      !same(candidateIdentity->get("format"), b[0]) ||
      !same(candidateIdentity->get("digest"), b[2]))
    return error("application-map-identity");
  const auto *applications = root->getArray("applications");
  const auto *instructions = root->getArray("instructions");
  if (!applications || !instructions)
    return error("application-map-schema");
  if (applications->size() > rowLimit || instructions->size() > rowLimit)
    return error("application-map-limit");
  if (auto e = compareInventory(source, candidate))
    return e;
  if (auto e = Checker(source, candidate, *applications, *instructions, budget)
                   .run())
    return e;
  return compareNative(source, candidate);
}
} // namespace zkc::protocol::application_map

namespace zkc::protocol {
Error checkApplicationMap(StringRef originalBytes, StringRef candidateBytes,
                          StringRef entry, StringRef mapBytes,
                          mlir::MLIRContext &context) {
  auto record = application_map::parseRecord(mapBytes);
  if (!record)
    return record.takeError();
  application_map::Budget budget;
  // Charge untrusted metadata before parsing or exporting the MLIR subjects.
  if (auto e = application_map::chargeTree(*record, budget))
    return e;
  auto source = application_map::readView(originalBytes, entry, context, budget,
                                          StructuredSourceProfile::Original);
  if (!source)
    return source.takeError();
  auto candidate =
      application_map::readView(candidateBytes, entry, context, budget,
                                StructuredSourceProfile::Prepared);
  if (!candidate)
    return candidate.takeError();
  return application_map::checkRecord(*source, *candidate, *record, budget);
}
} // namespace zkc::protocol
