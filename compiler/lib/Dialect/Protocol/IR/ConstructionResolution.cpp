#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Protocol/Construction.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSet.h"
#include <map>
#include <numeric>
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
namespace pir = protocol_ir;
using Path = SmallVector<std::string>;
struct Occurrence {
  Operation *operation;
  Path path;
  SmallVector<unsigned> services;
  SmallVector<Attribute> roles;
  std::optional<unsigned> authority;
};
bool within(ArrayRef<std::string> path, ArrayRef<std::string> parent) {
  return path.size() >= parent.size() &&
         equal(path.take_front(parent.size()), parent);
}
BlockArgument sourcePort(Value value) {
  while (auto argument = dyn_cast<BlockArgument>(value)) {
    auto repeat = dyn_cast<pir::RepeatOp>(argument.getOwner()->getParentOp());
    if (!repeat)
      return argument;
    if (!argument.getArgNumber())
      return {};
    value = repeat.getInputs()[argument.getArgNumber()];
  }
  return {};
}
class Resolver {
  SymbolTableCollection &symbols;
  uint64_t remaining = 1000000;
  llvm::StringSet<> active, definitions;
  std::map<Operation *, ConstructionPlan> plans;
  ResolvedConstruction result;
  Error fail(StringRef detail) {
    return error("protocol-construction", detail);
  }
  bool charge(uint64_t count) {
    if (count > remaining)
      return false;
    remaining -= count;
    return true;
  }
  bool chargePlan(const ConstructionPlan &plan) {
    if (!charge(1 + plan.rules.size() + plan.applications.size() +
                plan.state.size()))
      return false;
    for (const auto &rule : plan.rules) {
      if (!charge(1 + 2 * plan.state.size() + rule.inputs.size() +
                  2 * rule.payload.size() + 3 * rule.chunks.size() +
                  (plan.codec ? 2 * plan.codec->record.size() : 0)))
        return false;
      for (const auto &site : rule.sites)
        if (!charge(site.size() + 1))
          return false;
    }
    return true;
  }
  Expected<const ConstructionPlan &> read(pir::ConstructionOp record) {
    if (!charge(1))
      return fail("construction resolution work limit exceeded");
    auto found = plans.find(record);
    if (found != plans.end())
      return found->second;
    // Each definition is read once. Its bounded signature work is charged to
    // this traversal as well as each later occurrence's copying/expansion.
    auto checked = readConstructionPlan(record, symbols);
    if (!checked)
      return checked.takeError();
    if (!chargePlan(*checked))
      return fail("construction resolution work limit exceeded");
    return plans.emplace(record, std::move(*checked)).first->second;
  }
  Expected<std::string> site(ArrayRef<std::string> outer,
                             ArrayRef<std::string> path) {
    std::string value;
    for (auto parts : {outer, path})
      for (const auto &part : parts) {
        if (!charge(value.size() + part.size() + 1))
          return fail("construction resolution work limit exceeded");
        value = value.empty()
                    ? part
                    : mathematical::expandedApplicationSite(value, part);
        if (value.size() > 4096)
          return fail("expanded construction site exceeds limit");
      }
    return value;
  }
  Error inventory(pir::MathematicalOp function, Block &body,
                  ArrayRef<unsigned> services, ArrayRef<Attribute> roles,
                  ArrayRef<std::string> prefix, StringMap<Occurrence> &out,
                  unsigned depth) {
    if (depth > 64)
      return fail("construction occurrence depth exceeded");
    auto role = [&](Attribute name) -> Attribute {
      auto index =
          llvm::find(function.getRoles(), name) - function.getRoles().begin();
      return roles[index];
    };
    for (auto &op : body) {
      if (!charge(1))
        return fail("construction resolution work limit exceeded");
      if (auto repeat = dyn_cast<pir::RepeatOp>(op)) {
        if (auto e = inventory(function, repeat.getBody().front(), services,
                               roles, prefix, out, depth + 1))
          return e;
      }
      if (!isa<pir::ApplyOp, pir::QueryOp, pir::ExchangeOp>(op))
        continue;
      Path path(prefix.begin(), prefix.end());
      path.push_back(op.getAttrOfType<StringAttr>("site").str());
      auto name = site({}, path);
      if (!name)
        return name.takeError();
      Occurrence occurrence{&op, path, {}, {}, {}};
      auto authority = [&](Value value) -> std::optional<unsigned> {
        auto argument = sourcePort(value);
        if (!argument || argument.getOwner() != &function.getBody().front())
          return {};
        return services[argument.getArgNumber()];
      };
      if (auto query = dyn_cast<pir::QueryOp>(op)) {
        occurrence.authority = authority(query.getReference());
        if (!occurrence.authority)
          return fail("query lost its original service authority");
      }
      if (auto call = dyn_cast<pir::ApplyOp>(op)) {
        auto callee = symbols.lookupNearestSymbolFrom<pir::MathematicalOp>(
            call, call.getCalleeAttr());
        if (!callee)
          return fail("child call target is absent");
        occurrence.services.resize(call.getInputs().size());
        for (auto [i, value] : enumerate(call.getInputs())) {
          if (!isa<pir::ServiceReferenceType>(value.getType()))
            continue;
          auto port = authority(value);
          if (!port)
            return fail("call lost its original service authority");
          occurrence.services[i] = *port;
        }
        for (auto owner : call.getRoles())
          occurrence.roles.push_back(role(owner));
        if (auto e =
                inventory(callee, callee.getBody().front(), occurrence.services,
                          occurrence.roles, path, out, depth + 1))
          return e;
      }
      if (out.size() >= 2048 ||
          !out.try_emplace(*name, std::move(occurrence)).second)
        return fail("duplicate or oversized construction occurrence inventory");
    }
    return Error::success();
  }
  Error visit(pir::ConstructionOp record, ArrayRef<std::string> prefix,
              unsigned depth) {
    if (depth > 64 || !active.insert(record.getSymName()).second)
      return fail("cyclic or excessively deep construction composition");
    auto remove = llvm::scope_exit([&] { active.erase(record.getSymName()); });
    auto checked = read(record);
    if (!checked)
      return checked.takeError();
    const auto &plan = *checked;
    if (!chargePlan(plan))
      return fail("construction resolution work limit exceeded");
    if (definitions.insert(record.getSymName()).second)
      result.definitions.push_back(plan.symbol);
    auto target = symbols.lookupNearestSymbolFrom<pir::MathematicalOp>(
        record, plan.target);
    if (target.getRoles().size() != 2)
      return fail("construction composition requires two participants");
    StringMap<Occurrence> occurrences;
    SmallVector<unsigned> ports(target.getFunctionType().getNumInputs());
    std::iota(ports.begin(), ports.end(), 0);
    if (auto e = inventory(target, target.getBody().front(), ports,
                           target.getRoles().getValue(), {}, occurrences, 0))
      return e;
    SmallVector<const Occurrence *> children;
    for (const auto &selection : plan.applications) {
      auto found = occurrences.find(selection.site);
      if (found == occurrences.end() ||
          !isa<pir::ApplyOp>(found->second.operation))
        return fail("child selection names no protocol call");
      const auto &call = found->second;
      for (auto prior : children) {
        if (!charge(call.path.size() + prior->path.size()))
          return fail("construction resolution work limit exceeded");
        if (within(call.path, prior->path) || within(prior->path, call.path))
          return fail("construction applications overlap");
      }
      children.push_back(&call);
      auto child = symbols.lookupNearestSymbolFrom<pir::ConstructionOp>(
          record, selection.construction);
      auto childPlan = read(child);
      if (!childPlan)
        return childPlan.takeError();
      auto applied = cast<pir::ApplyOp>(call.operation);
      if (childPlan->target != applied.getCalleeAttr() || childPlan->rootOnly ||
          childPlan->nativeBase || childPlan->codec ||
          childPlan->provider != plan.provider ||
          childPlan->state != plan.state || childPlan->root != plan.root ||
          childPlan->suite != plan.suite ||
          childPlan->initializer != plan.initializer)
        return fail("child target, transcript root or authority differs");
      for (auto [port, type] : enumerate(applied.getOperandTypes()))
        if (isa<pir::ServiceReferenceType>(type) &&
            (is_contained(plan.services, call.services[port]) !=
             is_contained(childPlan->services, port)))
          return fail("child aliases the replaced authority through an "
                      "unselected port");
      auto childTarget = symbols.lookupNearestSymbolFrom<pir::MathematicalOp>(
          child, childPlan->target);
      auto parentOwners =
          cast<ArrayAttr>(target.getInputRoles()[plan.services.front()]);
      auto childOwners = cast<ArrayAttr>(
          childTarget.getInputRoles()[childPlan->services.front()]);
      if (childTarget.getRoles().size() != 2 || parentOwners.size() != 1 ||
          childOwners.size() != 1)
        return fail("child authority requires one verifier owner");
      auto owner = llvm::find(childTarget.getRoles(), childOwners[0]) -
                   childTarget.getRoles().begin();
      if (call.roles[owner] != parentOwners[0])
        return fail("child verifier mapping differs");
    }
    auto delegated = [&](const Occurrence &occurrence) -> Expected<bool> {
      for (auto call : children) {
        if (!charge(occurrence.path.size() + call->path.size()))
          return fail("construction resolution work limit exceeded");
        if (within(occurrence.path, call->path))
          return true;
      }
      return false;
    };
    llvm::StringSet<> covered;
    for (auto rule : plan.rules) {
      if (rule.kind == ConstructionRuleKind::Start) {
        if (prefix.empty())
          result.plan.rules.push_back(std::move(rule));
        else {
          auto name = site({}, prefix);
          if (!name)
            return name.takeError();
          result.invocations.push_back({*name, rule.handler, rule.inputs});
          if (result.invocations.size() > 2048)
            return fail("construction invocation limit exceeded");
        }
        continue;
      }
      bool codec = isCodecRule(rule.kind);
      for (auto &name : rule.sites) {
        auto found = occurrences.find(name);
        if (found == occurrences.end())
          return fail("construction rule names no protocol occurrence");
        const auto &occurrence = found->second;
        bool query = rule.kind == ConstructionRuleKind::Query;
        if ((query && (!isa<pir::QueryOp>(occurrence.operation) ||
                       !is_contained(plan.services, occurrence.authority))) ||
            (!query && !isa<pir::ExchangeOp>(occurrence.operation)))
          return fail("construction rule kind or authority differs");
        if (!codec) {
          auto owned = delegated(occurrence);
          if (!owned)
            return owned.takeError();
          if (*owned || !covered.insert(name).second)
            return fail(
                "construction handler overlaps a child or another handler");
        }
        auto expanded = site(prefix, occurrence.path);
        if (!expanded)
          return expanded.takeError();
        name = std::move(*expanded);
      }
      result.plan.rules.push_back(std::move(rule));
      if (result.plan.rules.size() > 2048)
        return fail("resolved construction rule limit exceeded");
    }
    if (!plan.nativeBase)
      for (const auto &item : occurrences) {
        const auto &occurrence = item.second;
        if (!isa<pir::ExchangeOp>(occurrence.operation) &&
            !(isa<pir::QueryOp>(occurrence.operation) &&
              is_contained(plan.services, occurrence.authority)))
          continue;
        auto owned = delegated(occurrence);
        if (!owned)
          return owned.takeError();
        if (!*owned && !covered.contains(item.getKey()))
          return fail((Twine("construction does not cover protocol site '") +
                       item.getKey() + "'")
                          .str());
      }
    for (auto [selection, call] : zip(plan.applications, children)) {
      Path childPath(prefix.begin(), prefix.end());
      append_range(childPath, call->path);
      auto child = symbols.lookupNearestSymbolFrom<pir::ConstructionOp>(
          record, selection.construction);
      if (auto e = visit(child, childPath, depth + 1))
        return e;
    }
    return Error::success();
  }

public:
  explicit Resolver(SymbolTableCollection &symbols) : symbols(symbols) {}
  Expected<ResolvedConstruction> run(pir::ConstructionOp record) {
    auto root = read(record);
    if (!root)
      return root.takeError();
    result.plan = *root;
    result.plan.rules.clear();
    result.plan.applications.clear();
    if (auto e = visit(record, {}, 0))
      return std::move(e);
    return std::move(result);
  }
};
} // namespace
Expected<ResolvedConstruction>
resolveConstructionPlan(pir::ConstructionOp record,
                        SymbolTableCollection &symbols) {
  return Resolver(symbols).run(record);
}
} // namespace zkc::protocol
