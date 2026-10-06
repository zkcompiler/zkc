#include "Run.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Source/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Protocol.h"
#include <map>
#include <set>

using namespace llvm;
using namespace mlir;
namespace zkc::detail {
namespace {
// Outer JSON costs seven nodes per step, one per role, and eleven fixed nodes.
// Keep emitted maxima within the run/1 decoder's 250000-node cap.
static_assert(32768 * 7 + 1024 + 11 <= 250000);
using Coordinate = std::pair<std::string, std::string>;
struct Role {
  const source::Participant *program;
  std::vector<const source::Instruction *> instructions;
  size_t cursor = 0;
};
class Schedule {
  std::vector<Role> roles;
  std::map<std::string, size_t> indices;
  std::map<Coordinate, std::string> calculations;
  std::set<Coordinate> guards;
  json::Array steps;
  json::Array *current = &steps;
  size_t stepCount = 0, nodes = 11, nextAnchor = 0;

  const source::Instruction *next(size_t role) const {
    const auto &r = roles[role];
    return r.cursor < r.instructions.size() ? r.instructions[r.cursor]
                                            : nullptr;
  }
  Error append(size_t role, std::optional<size_t> anchor) {
    if (++stepCount > 32768 || (nodes += 7) > 250000)
      return error("run-limit");
    json::Value group =
        anchor ? json::Value(int64_t(*anchor)) : json::Value(nullptr);
    current->push_back(
        json::Object{{"role", int64_t(role)},
                     {"instruction", int64_t(roles[role].cursor++)},
                     {"anchor", std::move(group)}});
    return Error::success();
  }
  Error prefix(size_t role, std::optional<size_t> anchor) {
    auto *instruction = next(role);
    if (!instruction)
      return error("run-incomplete");
    Coordinate key{roles[role].program->name, instruction->site};
    auto calculation = calculations.find(key);
    if (calculation == calculations.end() || guards.count(key))
      return Error::success();
    auto *call = instruction->get<source::LocalCall>();
    if (!call || call->callee != calculation->second)
      return error("run-calculation");
    calculations.erase(calculation);
    return append(role, anchor);
  }
  Expected<size_t> target(DictionaryAttr target) const {
    auto ref = target.getAs<FlatSymbolRefAttr>("participant");
    auto found = indices.find(ref.getValue().str());
    if (found == indices.end())
      return error("run-role");
    return found->second;
  }
  Error action(DictionaryAttr action, DictionaryAttr target, size_t anchor,
               bool withPrefix) {
    auto index = this->target(target);
    if (!index)
      return index.takeError();
    auto role = *index;
    if (withPrefix)
      if (auto e = prefix(role, anchor))
        return e;
    auto *instruction = next(role);
    auto site = action.getAs<StringAttr>("site").getValue();
    auto kind = target.getAs<StringAttr>("operation").getValue();
    if (!instruction || instruction->site != site)
      return error("run-occurrence");
    bool matches = false;
    if (kind == "protocol.finish_if")
      matches = bool(instruction->get<source::ReturnIf>());
    else if (kind == "protocol.send")
      matches = bool(instruction->get<source::Send>());
    else if (kind == "protocol.receive")
      matches = bool(instruction->get<source::Receive>());
    else if (kind == "protocol.service_query")
      matches = bool(instruction->get<source::ServiceQuery>());
    else if (kind == "local.call" || kind == "local.guard") {
      auto *call = instruction->get<source::LocalCall>();
      Coordinate key{roles[role].program->name, site.str()};
      if (kind == "local.guard") {
        auto calculation = calculations.find(key);
        matches = call && guards.count(key) &&
                  calculation != calculations.end() &&
                  call->callee == calculation->second;
        if (matches)
          calculations.erase(calculation);
      } else {
        auto callee = action.getAs<FlatSymbolRefAttr>("callee");
        matches = call && callee && call->callee == callee.getValue();
      }
    }
    if (!matches)
      return error("run-action");
    return append(role, anchor);
  }

  void collectGuards(ArrayAttr actions) {
    for (auto item : actions) {
      auto a = cast<DictionaryAttr>(item);
      if (auto body = a.getAs<ArrayAttr>("body"))
        collectGuards(body);
      if (a.getAs<StringAttr>("kind").getValue() == "protocol.guard")
        for (auto t : a.getAs<ArrayAttr>("targets"))
          guards.emplace(cast<DictionaryAttr>(t)
                             .getAs<FlatSymbolRefAttr>("participant")
                             .getValue()
                             .str(),
                         a.getAs<StringAttr>("site").str());
    }
  }
  Error buildActions(ArrayAttr actions, unsigned depth) {
    for (auto item : actions) {
      size_t anchor = nextAnchor++;
      auto a = cast<DictionaryAttr>(item);
      auto targets = a.getAs<ArrayAttr>("targets");
      if (a.getAs<StringAttr>("kind").getValue() == "protocol.repeat") {
        if (depth >= 64 || (nodes += 7) > 250000)
          return error("run-limit");
        json::Array entries, body, exits;
        auto *parent = current;
        current = &entries;
        std::vector<size_t> participants;
        for (auto targetItem : targets) {
          auto index = target(cast<DictionaryAttr>(targetItem));
          if (!index)
            return index.takeError();
          participants.push_back(*index);
          if (auto e = prefix(*index, anchor))
            return e;
          auto instruction = next(*index);
          auto loop = instruction ? instruction->get<source::Loop>() : nullptr;
          auto bound = a.getAs<IntegerAttr>("maximum");
          if (!loop || !bound || !a.getAs<ArrayAttr>("body") ||
              instruction->site != a.getAs<StringAttr>("site").getValue() ||
              loop->count.kind != source::LoopCount::Kind::Value ||
              loop->count.maximum != bound.getValue().getZExtValue())
            return error("run-loop");
          if (auto e = append(*index, anchor))
            return e;
        }
        current = &body;
        if (auto e = buildActions(a.getAs<ArrayAttr>("body"), depth + 1))
          return e;
        current = &exits;
        for (size_t role : participants) {
          if (auto e = prefix(role, std::nullopt))
            return e;
          auto instruction = next(role);
          if (!instruction || !instruction->get<source::Yield>())
            return error("run-yield");
          if (auto e = append(role, std::nullopt))
            return e;
        }
        current = parent;
        current->push_back(json::Object{{"loop", std::move(entries)},
                                        {"body", std::move(body)},
                                        {"yield", std::move(exits)}});
      } else if (a.getAs<StringAttr>("kind").getValue() ==
                 "protocol.exchange") {
        DictionaryAttr sender, receiver;
        for (auto t : targets) {
          auto target = cast<DictionaryAttr>(t);
          auto kind = target.getAs<StringAttr>("operation").getValue();
          if (kind == "protocol.send")
            sender = target;
          if (kind == "protocol.receive")
            receiver = target;
        }
        if (targets.size() != 2 || !sender || !receiver)
          return error("run-exchange");
        if (auto e = action(a, sender, anchor, true))
          return e;
        if (auto e = action(a, receiver, anchor, false))
          return e;
      } else {
        if (targets.size() != 1)
          return error("run-action");
        if (auto e = action(a, cast<DictionaryAttr>(targets[0]), anchor, true))
          return e;
      }
    }
    return Error::success();
  }

public:
  Expected<json::Array> build(const source::Participants &candidate,
                              DictionaryAttr interface, ArrayAttr origins) {
    auto roster = interface.getAs<ArrayAttr>("participants");
    if (roster.empty() || roster.size() > 1024)
      return error("run-limit");
    auto entry = interface.getAs<FlatSymbolRefAttr>("entry").getValue();
    auto selected = llvm::find_if(
        candidate.entries, [&](const auto &e) { return e.name == entry; });
    if (selected == candidate.entries.end() ||
        selected->participants.size() != roster.size())
      return error("run-entry");
    for (auto item : roster) {
      auto mapping = cast<DictionaryAttr>(item);
      auto symbol = mapping.getAs<FlatSymbolRefAttr>("participant").getValue();
      auto role = mapping.getAs<StringAttr>("role").getValue();
      auto found = llvm::find_if(candidate.participants, [&](const auto &p) {
        return p.name == symbol;
      });
      if (found == candidate.participants.end() || found->role != role ||
          !llvm::is_contained(selected->participants,
                              std::pair{role.str(), symbol.str()}) ||
          !indices.emplace(symbol.str(), roles.size()).second)
        return error("run-role");
      Role projected{&*found, {}, 0};
      source::walk(found->body, [&](const source::Instruction &instruction) {
        projected.instructions.push_back(&instruction);
      });
      roles.push_back(std::move(projected));
      ++nodes;
    }
    for (auto item : origins) {
      auto origin = cast<DictionaryAttr>(item);
      auto symbol = origin.getAs<FlatSymbolRefAttr>("participant").getValue();
      // Projection verification owns uniqueness; retain this defensive check
      // before constructing the schedule lookup.
      if (indices.count(symbol.str()) &&
          !calculations
               .emplace(
                   Coordinate{symbol.str(),
                              origin.getAs<StringAttr>("site").str()},
                   origin.getAs<FlatSymbolRefAttr>("callee").getValue().str())
               .second)
        return error("run-calculation", "duplicate calculation occurrence");
    }
    auto actions = interface.getAs<ArrayAttr>("actions");
    collectGuards(actions);
    if (auto e = buildActions(actions, 0))
      return e;
    for (size_t role = 0; role < roles.size(); ++role) {
      if (auto e = prefix(role, std::nullopt))
        return e;
      auto *instruction = next(role);
      if (!instruction || !instruction->get<source::Return>())
        return error("run-return");
      if (auto e = append(role, std::nullopt))
        return e;
      if (roles[role].cursor != roles[role].instructions.size())
        return error("run-coverage");
    }
    if (!calculations.empty())
      return error("run-calculation");
    return std::move(steps);
  }
};
} // namespace
Expected<std::string> buildRunBundle(ModuleOp prepared, ModuleOp module,
                                     StringRef entry) {
  auto roots = module.getOps<protocol_ir::ProtocolModuleOp>();
  if (!llvm::hasSingleElement(roots))
    return error("run-module");
  auto root = *roots.begin();
  auto records = root.getBody().front().getOps<protocol_ir::ProjectionOp>();
  if (!llvm::hasSingleElement(records))
    return error("run-projection");
  auto projection = *records.begin();
  DictionaryAttr selected;
  for (auto item : projection.getInterfaces()) {
    auto interface = cast<DictionaryAttr>(item);
    if (interface.getAs<FlatSymbolRefAttr>("entry").getValue() == entry)
      selected = interface;
  }
  if (!selected)
    return error("run-entry");
  auto content = protocol::exportSource(module);
  if (!content)
    return content.takeError();
  auto *candidate = std::get_if<source::Participants>(&*content);
  if (!candidate || !source::isProgram(candidate->contract) ||
      candidate->stage != source::Participants::Stage::Physical)
    return error("run-profile");
  if (auto e = source::checkStructure(*candidate))
    return e;
  auto steps =
      Schedule().build(*candidate, selected, projection.getCalculations());
  if (!steps)
    return steps.takeError();
  auto encoded = printJson(source::encode(*candidate));
  if (encoded.size() > 1024 * 1024)
    return error("run-limit");
  json::Array roles;
  for (auto role : selected.getAs<ArrayAttr>("roles")) {
    auto name = cast<StringAttr>(role).getValue();
    if (name.size() > 4096)
      return error("run-limit");
    roles.push_back(name.str());
  }
  auto bundle = printJson(json::Object{{"format", "zkc.run/1"},
                                       {"candidate", std::move(encoded)},
                                       {"entry", entry.str()},
                                       {"roles", std::move(roles)},
                                       {"steps", std::move(*steps)}});
  if (bundle.size() > 16 * 1024 * 1024)
    return error("run-limit");
  if (auto e = verifyRunBundle(prepared, module, bundle, entry))
    return std::move(e);
  return bundle;
}
} // namespace zkc::detail
