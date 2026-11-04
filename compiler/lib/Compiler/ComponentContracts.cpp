#include "ComponentContracts.h"
#include "SourceView.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Instances.h"
#include "zkc/Contracts/ResourceUnit.h"
#include "zkc/Contracts/SourceTerms.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Protocol/IR/RoleAttributes.h"
#include "zkc/Dialect/Relation/IR/Declarations.h"
#include "zkc/Dialect/Relation/IR/RelationOps.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/TypeSwitch.h"
#include <algorithm>
#include <deque>
#include <functional>
#include <map>
#include <memory>
#include <set>
#include <tuple>
using namespace llvm;
namespace zkc::language {
namespace {
using J = json::Value;
using A = json::Array;
using protocol::SourceBlock;
using protocol::SourceDefinition;
using protocol::SourceInstruction;
using protocol::SourceTerminator;
using protocol::SourceView;
StringRef symbol(mlir::Operation *op, StringRef attribute = "callee") {
  auto value = op->getAttrOfType<mlir::FlatSymbolRefAttr>(attribute);
  return value ? value.getValue() : StringRef();
}
// The owner of a single-owner action: a guard, a query or a local call; empty
// for every other operation.
StringRef role(mlir::Operation *op) {
  auto value = protocol_ir::getActionOwner(op);
  return value ? value.getValue() : StringRef();
}
std::vector<std::string> roleNames(mlir::ArrayAttr values) {
  std::vector<std::string> result;
  for (auto value : values)
    result.push_back(mlir::cast<mlir::StringAttr>(value).str());
  return result;
}
StringRef operationKind(mlir::Operation *op) {
  if (op->getName().getStringRef().starts_with("protocol.oracle_"))
    return "oracle_";
  return TypeSwitch<mlir::Operation *, StringRef>(op)
      .Case<protocol_ir::ApplyOp>([](auto) { return "protocol_apply"; })
      .Case<protocol_ir::RepeatOp>([](auto) { return "protocol_repeat"; })
      .Case<protocol_ir::RestrictRolesOp>([](auto) { return "restrict"; })
      .Case<protocol_ir::LocalCallOp>([](auto) { return "local_call"; })
      .Case<protocol_ir::QueryOp>([](auto) { return "draw"; })
      .Case<protocol_ir::ExchangeOp>([](auto) { return "exchange"; })
      .Case<protocol_ir::GuardOp>([](auto) { return "guard"; })
      .Case<protocol_ir::StatementOp>([](auto) { return "statement"; })
      .Case<data::FiniteFoldOp>([](auto) { return "fold"; })
      .Case<exec::ApplyOp>([](auto) { return "exec"; })
      .Case<exec::ComputeOp, exec::FoldOp, exec::CollectOp>(
          [](auto) { return "apply"; })
      .Case<exec::TestOp>([](auto) { return "if"; })
      .Case<exec::RangeOp>([](auto) { return "for"; })
      .Case<mlir::func::CallOp>([](auto) { return "call"; })
      .Case<mlir::arith::AndIOp>([](auto) { return "bool.and"; })
      .Default([&](auto) { return op->getName().getStringRef(); });
}
// These are source contract terms, not a serialized executable program. Their
// neutral data grammar is also owned by the MLIR-free Contracts component.
J contractTerm(mlir::Attribute attr) {
  if (mlir::isa<mlir::UnitAttr>(attr))
    return nullptr;
  if (auto value = mlir::dyn_cast<mlir::StringAttr>(attr))
    return value.getValue().str();
  if (auto value = mlir::dyn_cast<mlir::FlatSymbolRefAttr>(attr))
    return value.getValue().str();
  if (auto value = mlir::dyn_cast<mlir::IntegerAttr>(attr))
    return value.getInt();
  A result;
  for (auto value : mlir::cast<mlir::ArrayAttr>(attr))
    result.push_back(contractTerm(value));
  return result;
}
const A &array(const J &value) { return *value.getAsArray(); }
StringRef string(const J &value) { return *value.getAsString(); }
unsigned number(const J &value) { return *value.getAsUINT64(); }
mlir::ArrayAttr array(mlir::Attribute value) {
  return mlir::cast<mlir::ArrayAttr>(value);
}
StringRef string(mlir::Attribute value) {
  if (auto symbol = mlir::dyn_cast<mlir::FlatSymbolRefAttr>(value))
    return symbol.getValue();
  return mlir::cast<mlir::StringAttr>(value).getValue();
}
unsigned number(mlir::Attribute value) {
  return mlir::cast<mlir::IntegerAttr>(value).getValue().getZExtValue();
}
enum class RouteKind { Input, Result, RepeatInput, RepeatResult, Pure, Action };
struct Route {
  RouteKind kind;
  std::string site, role;
  unsigned result = 0;
  mlir::Operation *operation = nullptr;
  std::vector<unsigned> position, operands;
};
// Native provenance is a bounded interned DAG. Pending ownership uses node
// identities; only publication expands it into the external route grammar.
// Fixed-point loop analyses share this arena, so transferred facts keep their
// identities without encoding or reparsing a report.
class Routes {
  using Key = std::tuple<RouteKind, std::string, std::string, unsigned,
                         mlir::Operation *, std::vector<unsigned>,
                         std::vector<unsigned>>;
  std::map<Key, unsigned> names;
  std::vector<Route> nodes{{RouteKind::Input, {}, {}, 0, nullptr, {}, {}}};
  std::map<mlir::Operation *, J> descriptors;

public:
  unsigned intern(Route route) {
    Key key{route.kind,      route.site,     route.role,    route.result,
            route.operation, route.position, route.operands};
    auto [found, inserted] = names.emplace(std::move(key), nodes.size());
    if (inserted)
      nodes.push_back(std::move(route));
    return found->second;
  }
  bool direct(unsigned id) const {
    auto kind = nodes.at(id).kind;
    return kind != RouteKind::Pure && kind != RouteKind::Action;
  }
  Expected<J> encode(unsigned id, const SourceView &source,
                     bool acceptance = false) {
    const auto &route = nodes.at(id);
    StringRef tag;
    switch (route.kind) {
    case RouteKind::Input:
      return A{"input", route.result, route.role};
    case RouteKind::Result:
      tag = "result";
      break;
    case RouteKind::RepeatInput:
      tag = "repeat_input";
      break;
    case RouteKind::RepeatResult:
      tag = "repeat_result";
      break;
    case RouteKind::Pure:
    case RouteKind::Action: {
      tag = route.kind == RouteKind::Action ? "action" : "pure";
      bool pure = route.kind == RouteKind::Pure;
      if (acceptance && pure &&
          mlir::isa<protocol_ir::LocalCallOp, mlir::func::CallOp>(
              route.operation))
        tag = "terminal";
      A operands, position;
      for (unsigned child : route.operands) {
        auto value =
            encode(child, source,
                   acceptance && pure &&
                       mlir::isa<mlir::arith::AndIOp>(route.operation));
        if (!value)
          return value.takeError();
        operands.push_back(std::move(*value));
      }
      for (unsigned part : route.position)
        position.push_back(part);
      auto found = descriptors.find(route.operation);
      if (found == descriptors.end()) {
        auto descriptor =
            protocol::publishSourceDescriptor(source, *route.operation);
        if (!descriptor)
          return descriptor.takeError();
        found =
            descriptors.emplace(route.operation, std::move(*descriptor)).first;
      }
      return A{tag,          found->second, std::move(position),
               route.result, route.role,    std::move(operands)};
    }
    }
    return A{tag, route.site, route.result, route.role};
  }
};
struct Flow {
  unsigned route = 0;
  std::set<unsigned> pending;
  std::string effect;
  bool decision = false;
  unsigned nodes = 1;
  unsigned height = 1;
  bool acceptance = false;
};
using Family = std::map<std::string, Flow>;
using Environment = std::deque<Family>;
struct Deriver {
  const SourceView &program;
  std::shared_ptr<Routes> routes;
  std::map<std::string, const SourceDefinition *> functions;
  std::map<std::string, mlir::ArrayAttr> contracts;
  std::map<std::string, mlir::ArrayAttr> sources;
  std::map<std::string, relation::DeclareOp> relations;
  std::set<const void *> linear;
  struct Visible {
    std::string site;
    std::vector<mlir::Type> types;
    std::vector<std::set<std::string>> scopes;
  };
  struct CallContext {
    const SourceDefinition *caller;
    const SourceDefinition *callee;
    std::vector<Visible> visible;
  };
  std::map<std::pair<std::string, std::string>, CallContext> contexts;
  A rows, proposals;
  unsigned visits = 0;
  Error failure = Error::success();
  explicit Deriver(const SourceView &value,
                   std::shared_ptr<Routes> routes = std::make_shared<Routes>())
      : program(value), routes(std::move(routes)) {
    for (const auto &definition : value.definitions) {
      if (definition.kind == "oracle" || !definition.hasBody)
        continue;
      functions.emplace(definition.name, &definition);
      if (auto protocol = mlir::dyn_cast<protocol_ir::MathematicalOp>(
              definition.operation)) {
        contracts.emplace(
            definition.name,
            protocol.getContractsAttr()
                ? protocol.getContractsAttr()
                : mlir::ArrayAttr::get(protocol.getContext(), {}));
      }
    }
    auto unit = mlir::cast<protocol_ir::ProtocolModuleOp>(
        value.native.get().getBody()->front());
    for (auto declaration :
         unit.getBody().front().getOps<relation::DeclareOp>())
      relations.emplace(declaration.getSymName().str(), declaration);
    auto tables = unit->getAttrOfType<mlir::ArrayAttr>("source_declarations");
    if (!tables)
      return;
    for (const auto &value : array(tables[0])) {
      auto record = array(value);
      if (string(record[1]) == "linear")
        linear.insert(termKey(record[0]));
    }
    for (const auto &value : array(tables[1])) {
      auto source = array(value);
      sources.emplace(string(source[0]), source);
    }
  }
  bool refuse(StringRef code) {
    if (!failure)
      failure = error(code);
    return false;
  }
  bool charge(unsigned work = 1) {
    if (work > 100000 - visits)
      return refuse("component-seam-limit");
    visits += work;
    return true;
  }
  const void *termKey(mlir::Attribute term) {
    uint64_t remaining = 100000 - visits;
    auto normalized = canonicalDeclarationTerm(term, remaining);
    visits = 100000 - remaining;
    if (!normalized) {
      consumeError(normalized.takeError());
      refuse("component-seam-limit");
      return nullptr;
    }
    return normalized->getAsOpaquePointer();
  }
  bool pendingPort(mlir::ArrayAttr port) {
    return linear.count(termKey(port[1]));
  }
  Flow leaf(RouteKind kind, StringRef site, unsigned result, StringRef role,
            bool pending = false) {
    unsigned id =
        routes->intern({kind, site.str(), role.str(), result, nullptr, {}, {}});
    return {
        id, pending ? std::set<unsigned>{id} : std::set<unsigned>{}, {}, false};
  }
  template <typename Sequence>
  bool read(const Sequence &environment, unsigned index, StringRef role,
            Flow &flow) {
    if (index >= environment.size())
      return refuse("component-seam-reference");
    auto found = environment[index].find(role.str());
    if (found == environment[index].end())
      return refuse("component-seam-role");
    flow = found->second;
    return true;
  }
  bool methodEffect(StringRef effect) {
    return effect == "component-seam-sampling" ||
           effect == "component-seam-message";
  }
  // A refusal dominates an admitted method effect. Existing nonempty effects
  // otherwise win, so each loop input changes at most twice during closure.
  std::string joinEffect(StringRef first, StringRef second) {
    return (first.empty() ||
            (methodEffect(first) && !second.empty() && !methodEffect(second)))
               ? second.str()
               : first.str();
  }
  bool pure(const Flow &flow, bool method = false) {
    return flow.effect.empty() || (method && methodEffect(flow.effect)) ||
           refuse(flow.effect);
  }
  bool consume(const std::vector<Flow> &flows, std::set<unsigned> &live,
               bool method = false) {
    std::set<unsigned> used;
    std::set<unsigned> projections;
    for (const auto &flow : flows) {
      if (!pure(flow, method))
        return false;
      if (!flow.pending.empty() && !projections.insert(flow.route).second)
        return refuse("component-seam-coverage");
      used.insert(flow.pending.begin(), flow.pending.end());
    }
    for (const auto &value : used)
      if (!live.erase(value))
        return refuse("component-seam-coverage");
    return true;
  }
  void row(StringRef caller, J endpoint, const std::vector<Flow> &flows,
           StringRef explicitKind = {}) {
    if (failure)
      return;
    A routes;
    bool direct = true, method = false;
    for (const auto &flow : flows) {
      auto encoded = this->routes->encode(flow.route, program, flow.acceptance);
      if (!encoded) {
        failure = encoded.takeError();
        return;
      }
      routes.push_back(std::move(*encoded));
      direct &= this->routes->direct(flow.route);
      method |= !flow.effect.empty();
    }
    rows.push_back(A{caller.str(), std::move(endpoint),
                     explicitKind.empty() ? (method   ? "method"
                                             : direct ? "direct"
                                                      : "pure")
                                          : explicitKind.str(),
                     std::move(routes)});
  }
  const std::vector<std::string> &roles(const SourceDefinition &function) {
    return function.roles;
  }
  bool makeInputs(const SourceDefinition &function, Environment &environment,
                  std::set<unsigned> &live) {
    StringRef name = function.name;
    const auto &types = function.body.inputs;
    const auto &scopes = function.inputRoles;
    auto source =
        sources.count(name.str()) ? sources.at(name.str()) : mlir::ArrayAttr();
    for (unsigned i = 0; i < types.size(); ++i) {
      bool pending = false;
      if (source)
        for (auto value : array(source[1])) {
          const auto &port = array(value);
          if (number(port[3]) <= i && i < number(port[3]) + number(port[4]))
            pending = pendingPort(port);
        }
      Family family;
      for (const auto &role : scopes[i]) {
        auto flow = leaf(RouteKind::Input, {}, i, role, pending);
        live.insert(flow.pending.begin(), flow.pending.end());
        family.emplace(role, std::move(flow));
      }
      environment.push_back(std::move(family));
    }
    return true;
  }
  bool block(const SourceDefinition &function, const SourceBlock &body,
             Environment environment, std::set<unsigned> live,
             std::vector<unsigned> path, std::vector<Family> &returned,
             unsigned depth = 0, std::vector<Visible> visible = {}) {
    if (depth > 64)
      return refuse("component-seam-depth");
    StringRef caller = function.name;
    auto roster = roles(function);
    std::set<unsigned> guarded;
    unsigned ordinal = 0;
    for (const auto &instruction : body.instructions) {
      if (!charge())
        return false;
      auto *op = instruction.operation;
      auto tag = operationKind(op);
      StringRef site = instruction.site;
      const auto &args = instruction.operands;
      const auto &types = instruction.results;
      auto position = path;
      position.push_back(ordinal++);
      std::vector<Family> results(types.size());
      if (tag == "protocol_apply") {
        auto found = functions.find(symbol(op).str());
        if (found == functions.end())
          return refuse("component-seam-call");
        const auto &callee = *found->second;
        auto childRoles = roles(callee);
        const auto actualRoles =
            roleNames(mlir::cast<protocol_ir::ApplyOp>(op).getRoles());
        auto actual = [&](StringRef role) -> StringRef {
          size_t index =
              std::find(childRoles.begin(), childRoles.end(), role.str()) -
              childRoles.begin();
          return index < actualRoles.size() ? StringRef(actualRoles[index])
                                            : StringRef();
        };
        auto source = sources.find(callee.name);
        if (source != sources.end()) {
          unsigned portIndex = 0;
          for (auto value : array(source->second[1])) {
            const auto &port = array(value);
            if (pendingPort(port)) {
              std::vector<Flow> flows;
              for (unsigned i = 0; i < number(port[4]); ++i) {
                Flow flow;
                if (!read(environment, args[number(port[3]) + i],
                          actual(string(array(port[2])[0])), flow))
                  return false;
                flows.push_back(std::move(flow));
              }
              row(caller, A{"argument", site.str(), portIndex}, flows);
              if (!consume(flows, live, true))
                return false;
            }
            ++portIndex;
          }
        }
        const auto &outputScopes = callee.outputRoles;
        for (unsigned i = 0; i < results.size(); ++i) {
          bool pending = false, decision = false;
          if (source != sources.end())
            for (auto value : array(source->second[2])) {
              const auto &port = array(value);
              if (number(port[3]) <= i && i < number(port[3]) + number(port[4]))
                pending = pendingPort(port);
            }
          for (const auto &value : contracts.at(callee.name)) {
            const auto &clause = array(value);
            if (!mlir::isa<mlir::UnitAttr>(clause[4]) &&
                number(array(clause[4])[1]) == i)
              decision = true;
          }
          for (const auto &role : outputScopes[i]) {
            auto flow = leaf(RouteKind::Result, site, i, actual(role), pending);
            flow.decision =
                decision &&
                std::any_of(contracts.at(callee.name).begin(),
                            contracts.at(callee.name).end(),
                            [&](mlir::Attribute value) {
                              const auto &clause = array(value);
                              return !mlir::isa<mlir::UnitAttr>(clause[4]) &&
                                     number(array(clause[4])[1]) == i &&
                                     string(array(clause[4])[2]) == role;
                            });
            live.insert(flow.pending.begin(), flow.pending.end());
            results[i].emplace(actual(role), std::move(flow));
          }
        }
        // Proposals are per actual call, even when the callee has no logical
        // slots.
        A slots;
        for (const auto &value : contracts.at(callee.name)) {
          const auto &clause = array(value);
          for (unsigned side : {2u, 3u}) {
            if (mlir::isa<mlir::UnitAttr>(clause[side]))
              continue;
            const auto &application = array(clause[side]);
            auto found = relations.find(string(application[0]).str());
            if (found == relations.end())
              return refuse("component-instantiation");
            const auto &selectors = array(application[1]);
            auto purposes = found->second.getPurposes();
            for (unsigned i = 0; i < selectors.size(); ++i) {
              if (mlir::cast<mlir::StringAttr>(purposes[i]).getValue() ==
                  "statement")
                continue;
              J slot = A{mlir::cast<mlir::StringAttr>(purposes[i]).getValue(),
                         contractTerm(selectors[i]), A{"open"}};
              if (std::find(slots.begin(), slots.end(), slot) == slots.end()) {
                if (slots.size() == 512)
                  return refuse("component-instantiation-limit");
                slots.push_back(std::move(slot));
              }
            }
          }
        }
        if (!contexts
                 .emplace(std::make_pair(caller.str(), site.str()),
                          CallContext{&function, &callee, visible})
                 .second)
          return refuse("component-instantiation");
        A arguments, mappedRoles;
        for (unsigned operand : args)
          arguments.push_back(operand);
        for (const auto &name : actualRoles)
          mappedRoles.push_back(name);
        proposals.push_back(A{caller.str(), site.str(), callee.name,
                              std::move(arguments), std::move(mappedRoles),
                              std::move(slots)});
      } else if (tag == "protocol_repeat") {
        unsigned carried = mlir::cast<protocol_ir::RepeatOp>(op).getCarried();
        if (instruction.regions.size() != 1)
          return refuse("component-seam-control");
        const auto &region = instruction.regions[0];
        Environment inner;
        std::set<unsigned> innerLive;
        std::vector<bool> marked(args.size(), false);
        std::vector<Flow> initialFlows;
        if (args.empty() || args[0] >= environment.size())
          return refuse("component-seam-reference");
        Flow count;
        for (const auto &[role, flow] : environment[args[0]])
          count.effect = joinEffect(count.effect, flow.effect);
        for (unsigned i = 0; i < args.size(); ++i) {
          Family family;
          if (args[i] >= environment.size())
            return refuse("component-seam-reference");
          for (const auto &[role, flow] : environment[args[i]]) {
            bool pending = i > 0 && i <= carried && !flow.pending.empty();
            if (i > 0 && i <= carried)
              row(caller, A{"repeat_init", site.str(), i - 1, role}, {flow});
            if (pending) {
              initialFlows.push_back(flow);
              marked[i] = true;
            } else if (!flow.pending.empty())
              return refuse("component-seam-control");
            auto input = leaf(RouteKind::RepeatInput, site, i, role, pending);
            input.effect =
                i == 0 ? flow.effect : joinEffect(flow.effect, count.effect);
            innerLive.insert(input.pending.begin(), input.pending.end());
            family.emplace(role, std::move(input));
          }
          inner.push_back(std::move(family));
        }
        // Flattened fields of one representation share ancestry. Transfer the
        // complete carried tuple once, retaining every projection obligation.
        if (!consume(initialFlows, live, true))
          return false;
        std::vector<Family> yielded;
        auto nested = position;
        nested.push_back(0);
        unsigned carriedFlows = 0;
        for (unsigned i = 1; i <= carried; ++i)
          carriedFlows += inner[i].size();
        bool stable = false;
        // Reuse the actual traversal, discarding candidate rows until effects
        // close over every carried backedge. All candidate work is charged.
        for (unsigned pass = 0; pass <= 2 * carriedFlows; ++pass) {
          Deriver candidate(program, routes);
          candidate.visits = visits;
          candidate.contexts = contexts;
          yielded.clear();
          if (!candidate.block(function, region, inner, innerLive, nested,
                               yielded, depth + 1, {})) {
            failure = std::move(candidate.failure);
            return false;
          }
          visits = candidate.visits;
          if (yielded.size() != carried)
            return refuse("component-seam-control");
          stable = true;
          for (unsigned i = 0; i < carried; ++i)
            for (auto &[role, input] : inner[i + 1]) {
              Flow output;
              if (!read(yielded, i, role, output))
                return false;
              auto effect = joinEffect(input.effect, output.effect);
              stable &= effect == input.effect;
              input.effect = std::move(effect);
            }
          if (stable) {
            for (auto &value : candidate.rows)
              rows.push_back(std::move(value));
            for (auto &value : candidate.proposals)
              proposals.push_back(std::move(value));
            contexts = std::move(candidate.contexts);
            break;
          }
        }
        if (!stable)
          return refuse("component-seam-limit");
        // These rows associate each fresh boundary leaf with its original
        // source, the count, and (for carried values) its yielded alternative.
        for (unsigned i = 0; i < args.size(); ++i)
          for (const auto &[role, flow] : environment[args[i]]) {
            std::vector<Flow> dependencies{flow};
            if (i > 0)
              for (const auto &[_, control] : environment[args[0]])
                dependencies.push_back(control);
            if (i > 0 && i <= carried) {
              Flow output;
              if (!read(yielded, i - 1, role, output))
                return false;
              dependencies.push_back(std::move(output));
            }
            row(caller, A{"repeat_input", site.str(), i, role}, dependencies);
          }
        for (unsigned i = 0; i < carried; ++i)
          for (const auto &role : roleNames(mlir::cast<mlir::ArrayAttr>(
                   mlir::cast<protocol_ir::RepeatOp>(op)
                       .getCarriedRoles()[i]))) {
            auto found = yielded[i].find(role);
            if (found == yielded[i].end())
              return refuse("component-seam-role");
            Flow initial;
            if (!read(environment, args[i + 1], role, initial))
              return false;
            auto controlled = found->second;
            controlled.effect = joinEffect(controlled.effect, count.effect);
            row(caller, A{"yield", site.str(), i, role}, {controlled});
            // Both alternatives are retained: zero iterations returns initial
            // state. The matching repeat_input row also retains count control.
            row(caller, A{"repeat_result", site.str(), i, role},
                {initial, controlled});
            auto flow =
                leaf(RouteKind::RepeatResult, site, i, role, marked[i + 1]);
            flow.effect = joinEffect(joinEffect(initial.effect, count.effect),
                                     found->second.effect);
            live.insert(flow.pending.begin(), flow.pending.end());
            results[i].emplace(role, std::move(flow));
          }
      } else {
        // Logical oracle routes need anchor-aware seams. Do not classify a new
        // oracle instruction as a pure value merely because its descriptor is
        // outside the old effect cases. Export and seam admission are separate.
        if (tag.starts_with("oracle_"))
          return refuse("component-seam-oracle");
        if (!instruction.regions.empty())
          return refuse("component-seam-control");
        if (tag == "statement")
          continue;
        if (tag == "guard") {
          Flow flow;
          if (!read(environment, args[0], role(op), flow))
            return false;
          if (!flow.pending.empty()) {
            row(caller, A{"guard", site.str(), role(op)}, {flow}, "method");
            if (!pure(flow, true))
              return false;
            for (const auto &pending : flow.pending) {
              if (!live.count(pending))
                return refuse("component-seam-coverage");
              guarded.insert(pending);
            }
          }
          continue;
        }
        auto exchange = mlir::dyn_cast<protocol_ir::ExchangeOp>(op);
        for (const auto &role : roster) {
          if (tag == "restrict" &&
              !llvm::is_contained(
                  roleNames(
                      mlir::cast<protocol_ir::RestrictRolesOp>(op).getRoles()),
                  role))
            continue;
          if ((tag == "local_call" || tag == "draw") &&
              zkc::language::role(op) != role)
            continue;
          if (exchange && exchange.getReceiver() != role)
            continue;
          std::vector<Flow> operands;
          bool available = true;
          for (const auto &argument : args) {
            unsigned index = argument;
            if (index >= environment.size())
              return refuse("component-seam-reference");
            auto sourceRole = exchange ? exchange.getSender().str() : role;
            auto found = environment[index].find(sourceRole);
            if (found == environment[index].end()) {
              available = false;
              break;
            }
            operands.push_back(found->second);
          }
          if (!available)
            continue;
          unsigned nodes = 1;
          for (const auto &operand : operands) {
            if (operand.nodes > 100000 - nodes)
              return refuse("component-seam-limit");
            nodes += operand.nodes;
          }
          if (types.size() > 100000 / nodes || !charge(nodes * types.size()))
            return refuse("component-seam-limit");
          std::vector<unsigned> operandRoutes;
          Flow aggregate;
          for (const auto &operand : operands) {
            operandRoutes.push_back(operand.route);
            aggregate.nodes += operand.nodes;
            aggregate.height = std::max(aggregate.height, operand.height + 1);
            aggregate.pending.insert(operand.pending.begin(),
                                     operand.pending.end());
            aggregate.effect = joinEffect(aggregate.effect, operand.effect);
          }
          if (aggregate.height > 64)
            return refuse("component-seam-depth");
          if (tag == "draw" || tag == "exchange") {
            if (aggregate.effect.empty() || methodEffect(aggregate.effect))
              aggregate.effect = tag == "draw" ? "component-seam-sampling"
                                               : "component-seam-message";
          } else if (tag == "apply" || tag == "fold")
            aggregate.effect = "component-seam-effect";
          else if (tag == "call" || tag == "local_call") {
            auto found = functions.find(symbol(op).str());
            if (found == functions.end())
              return refuse("component-seam-call");
            if (tag == "call" && found->second->kind != "math")
              aggregate.effect = "component-seam-effect";
            if (tag == "local_call" && !deterministic(*found->second, 0))
              return false;
          }
          for (unsigned i = 0; i < types.size(); ++i) {
            auto flow = aggregate;
            flow.route =
                tag == "restrict"
                    ? operands[0].route
                    : routes->intern({tag == "draw" || tag == "exchange"
                                          ? RouteKind::Action
                                          : RouteKind::Pure,
                                      {},
                                      role,
                                      i,
                                      op,
                                      position,
                                      operandRoutes});
            if (tag == "local_call" && aggregate.pending.empty() &&
                aggregate.effect.empty())
              flow.route = routes->intern(
                  {RouteKind::Result, site.str(), role, i, nullptr, {}, {}});
            // Every output projection of a Local representation map must
            // subsequently be covered, even when it shares input ancestry.
            if (tag == "local_call" && !aggregate.pending.empty()) {
              auto projection = flow.route;
              flow.pending.insert(projection);
              live.insert(std::move(projection));
            }
            flow.decision =
                (tag == "local_call" || tag == "call") && types[i].isInteger(1);
            if (tag == "bool.and")
              flow.decision =
                  (operands[0].decision || operands[0].pending.empty()) &&
                  (operands[1].decision || operands[1].pending.empty());
            results[i].emplace(role, std::move(flow));
          }
        }
      }
      std::vector<std::set<std::string>> scopes;
      for (const auto &family : results) {
        std::set<std::string> roles;
        for (const auto &[role, _] : family)
          roles.insert(role);
        scopes.push_back(std::move(roles));
      }
      visible.push_back({site.str(), types, std::move(scopes)});
      environment.insert(environment.begin(), results.begin(), results.end());
    }
    if (body.terminator == SourceTerminator::Stop) {
      returned.clear();
      return true;
    }
    if (body.terminator != SourceTerminator::Return &&
        body.terminator != SourceTerminator::Yield)
      return refuse("component-seam-control");
    for (unsigned index : body.returned) {
      if (index >= environment.size())
        return refuse("component-seam-reference");
      returned.push_back(environment[index]);
    }
    if (body.terminator == SourceTerminator::Yield) {
      std::vector<Flow> flows;
      for (const auto &family : returned)
        for (const auto &[role, flow] : family)
          if (!flow.pending.empty())
            flows.push_back(flow);
      if (!consume(flows, live, true))
        return false;
    } else {
      auto source = sources.find(caller.str());
      if (source != sources.end()) {
        unsigned portIndex = 0;
        for (auto value : array(source->second[2])) {
          const auto &port = array(value);
          if (pendingPort(port)) {
            std::vector<Flow> flows;
            for (unsigned i = 0; i < number(port[4]); ++i) {
              Flow flow;
              if (!read(returned, number(port[3]) + i,
                        string(array(port[2])[0]), flow))
                return false;
              flows.push_back(std::move(flow));
            }
            row(caller, A{"output", portIndex, "residual"}, flows);
            if (!consume(flows, live, true))
              return false;
          }
          ++portIndex;
        }
      }
      unsigned clauseIndex = 0;
      std::set<std::pair<unsigned, std::string>> acceptedOutputs;
      for (const auto &value : contracts.at(caller.str())) {
        const auto &clause = array(value);
        if (!mlir::isa<mlir::UnitAttr>(clause[4])) {
          const auto &decision = array(clause[4]);
          Flow flow;
          if (!read(returned, number(decision[1]), string(decision[2]), flow))
            return false;
          if (!flow.pending.empty()) {
            if (!flow.decision)
              return refuse("component-seam-acceptance");
            if (!pure(flow))
              return false;
            // Several clauses may select one acceptance output. Distinct
            // outputs and previous consumers cannot reuse its ownership.
            if (acceptedOutputs
                    .emplace(number(decision[1]), string(decision[2]).str())
                    .second &&
                !consume({flow}, live))
              return false;
            // Only conjunction propagates terminal acceptance into child
            // routes. The native operation kind controls that publication.
            flow.acceptance = true;
            row(caller, A{"output", number(decision[1]), clauseIndex}, {flow},
                "terminal");
          }
        }
        ++clauseIndex;
      }
    }
    for (const auto &pending : guarded)
      live.erase(pending);
    return live.empty() || refuse("component-seam-coverage");
  }
  bool run() {
    if (failure)
      return false;
    // Anchor contracts require the oracle-store interpretation. Refuse them
    // before any data-only slot traversal; a data ABI cannot resolve an anchor.
    for (const auto &[name, clauses] : contracts)
      for (auto value : clauses) {
        const auto &clause = array(value);
        for (unsigned side : {2u, 3u}) {
          if (mlir::isa<mlir::UnitAttr>(clause[side]))
            continue;
          for (const auto &value : array(array(clause[side])[1])) {
            if (!charge())
              return false;
            if (string(array(value)[0]) == "anchor")
              return refuse("component-seam-oracle");
          }
        }
      }

    if (linear.empty())
      return true;
    std::map<const void *, std::string> meanings;
    for (const auto &[name, source] : sources) {
      for (unsigned side : {1u, 2u})
        for (auto value : array(source[side])) {
          const auto &port = array(value);
          if (!pendingPort(port))
            continue;
          if (array(port[2]).size() != 1 || !number(port[4]))
            return refuse("component-claim-role");
          // The selected protocol may be a library root with linear ports.
          // Concrete Entry target/acceptance checks belong to claim selection.
          // Clause-free wrappers assert no relation; their resource ownership
          // is still checked by the traversal below.
          if (contracts.at(name).empty())
            continue;
          std::set<std::string> relations;
          for (const auto &value : contracts.at(name)) {
            const auto &clause = array(value);
            for (unsigned part : {2u, 3u}) {
              if (mlir::isa<mlir::UnitAttr>(clause[part]))
                continue;
              const auto &application = array(clause[part]);
              for (const auto &value : array(application[1])) {
                const auto &selector = array(value);
                if (string(selector[0]) == (side == 1 ? "input" : "output") &&
                    number(port[3]) <= number(selector[1]) &&
                    number(selector[1]) < number(port[3]) + number(port[4]))
                  relations.insert(string(application[0]).str());
              }
            }
          }
          if (relations.size() != 1)
            return refuse("component-claim-relation");
          auto [previous, added] =
              meanings.emplace(termKey(port[1]), *relations.begin());
          if (!added && previous->second != *relations.begin())
            return refuse("component-claim-relation");
        }
    }
    for (const auto &[name, function] : functions) {
      if (function->kind != "protocol")
        continue;
      Environment inputs;
      std::set<unsigned> live;
      std::vector<Family> returned;
      if (!makeInputs(*function, inputs, live) ||
          !block(*function, function->body, std::move(inputs), std::move(live),
                 {}, returned))
        return false;
    }
    return true;
  }
  bool logicalSlot(const SourceDefinition &owner, StringRef purpose,
                   const J &selector) {
    for (const auto &value : contracts.at(owner.name)) {
      const auto &clause = array(value);
      for (unsigned side : {2u, 3u}) {
        if (mlir::isa<mlir::UnitAttr>(clause[side]))
          continue;
        const auto &application = array(clause[side]);
        auto found = relations.find(string(application[0]).str());
        if (found == relations.end())
          continue;
        const auto &selectors = array(application[1]);
        auto purposes = found->second.getPurposes();
        for (unsigned i = 0; i < selectors.size(); ++i)
          if (contractTerm(selectors[i]) == selector &&
              mlir::cast<mlir::StringAttr>(purposes[i]).getValue() == purpose)
            return true;
      }
    }
    return false;
  }
  bool source(const J &value, mlir::Type expected, const CallContext &context,
              const A &proposal,
              const std::vector<std::set<std::string>> &allowed,
              unsigned depth = 0) {
    if (!charge() || depth > 64)
      return refuse("component-instantiation");
    const auto *parts = value.getAsArray();
    if (!parts || parts->empty() || !(*parts)[0].getAsString())
      return refuse("component-instantiation");
    const auto &items = *parts;
    auto tag = string(items[0]);
    auto permit = [&](StringRef role) {
      return !allowed.empty() && std::all_of(allowed.begin(), allowed.end(),
                                             [&](const auto &roles) {
                                               return roles.count(role.str());
                                             });
    };
    auto index = [&](const J &value, llvm::ArrayRef<mlir::Type> types) {
      auto number = value.getAsUINT64();
      return number && *number < types.size() && types[*number] == expected;
    };
    if (tag == "open")
      return (items.size() == 1 && depth == 0) ||
             refuse("component-instantiation");
    if (tag == "operand" && items.size() == 3 && items[1].getAsUINT64() &&
        items[2].getAsString()) {
      const auto &callee = *context.callee;
      if (!index(items[1], callee.body.inputs) || !permit(string(items[2])))
        return refuse("component-instantiation");
      for (const auto &role : callee.inputRoles[number(items[1])]) {
        const auto &roles = callee.roles;
        auto found = std::find(roles.begin(), roles.end(), role);
        if (found != roles.end() &&
            array(proposal[4])[found - roles.begin()] == items[2])
          return true;
      }
      return refuse("component-instantiation");
    }
    if ((tag == "parameter" || tag == "witness") && items.size() == 2) {
      auto selected = items[1].getAsArray();
      if (!selected || selected->size() != 3 || (*selected)[0] != J("input") ||
          !(*selected)[1].getAsUINT64() || !(*selected)[2].getAsString())
        return refuse("component-instantiation");
      const auto &owner = *context.caller;
      if (!index((*selected)[1], owner.body.inputs) ||
          !permit(string((*selected)[2])) || !logicalSlot(owner, tag, items[1]))
        return refuse("component-instantiation");
      const auto &scope = owner.inputRoles[number((*selected)[1])];
      return llvm::is_contained(scope, string((*selected)[2]).str()) ||
             refuse("component-instantiation");
    }
    if (tag == "result" && items.size() == 4 && items[1].getAsString() &&
        items[2].getAsUINT64() && items[3].getAsString()) {
      const Visible *selected = nullptr;
      for (const auto &value : context.visible)
        if (value.site == string(items[1])) {
          if (selected)
            return refuse("component-instantiation");
          selected = &value;
        }
      if (!selected || !index(items[2], selected->types) ||
          !permit(string(items[3])))
        return refuse("component-instantiation");
      return selected->scopes[number(items[2])].count(string(items[3]).str()) ||
             refuse("component-instantiation");
    }
    if (tag == "math" && items.size() == 4 && items[1].getAsString() &&
        items[2].getAsUINT64() && items[3].getAsArray()) {
      auto found = functions.find(string(items[1]).str());
      if (found == functions.end())
        return refuse("component-instantiation");
      const auto &helper = *found->second;
      if (helper.kind != "math" || !index(items[2], helper.body.outputs) ||
          array(items[3]).size() != helper.body.inputs.size())
        return refuse("component-instantiation");
      for (unsigned i = 0; i < array(items[3]).size(); ++i)
        if (!source(array(items[3])[i], helper.body.inputs[i], context,
                    proposal, allowed, depth + 1))
          return false;
      return true;
    }
    return refuse("component-instantiation");
  }
  bool check(const json::Object &actual) {
    auto actualRows = actual.getArray("seams"),
         actualCalls = actual.getArray("proposals");
    if (!actualRows || *actualRows != rows)
      return refuse("component-seam-association");
    if (!actualCalls || actualCalls->size() != proposals.size())
      return refuse("component-instantiation");
    for (unsigned i = 0; i < proposals.size(); ++i) {
      auto proposed = (*actualCalls)[i].getAsArray();
      const auto &canonical = array(proposals[i]);
      if (!proposed || proposed->size() != 6)
        return refuse("component-instantiation");
      for (unsigned field = 0; field < 5; ++field)
        if ((*proposed)[field] != canonical[field])
          return refuse("component-instantiation");
      auto slots = (*proposed)[5].getAsArray();
      if (!slots || slots->size() != array(canonical[5]).size())
        return refuse("component-instantiation");
      const auto &context =
          contexts.at({string(canonical[0]).str(), string(canonical[1]).str()});
      const auto &callee = *context.callee;
      for (unsigned j = 0; j < slots->size(); ++j) {
        auto slot = (*slots)[j].getAsArray();
        const auto &expectedSlot = array(array(canonical[5])[j]);
        if (!slot || slot->size() != 3 || (*slot)[0] != expectedSlot[0] ||
            (*slot)[1] != expectedSlot[1])
          return refuse("component-instantiation");
        const auto &selector = array((*slot)[1]);
        const auto &types = selector[0] == J("input") ? callee.body.inputs
                                                      : callee.body.outputs;
        std::vector<std::set<std::string>> allowed;
        for (const auto &value : contracts.at(callee.name)) {
          const auto &clause = array(value);
          for (unsigned side : {2u, 3u}) {
            if (mlir::isa<mlir::UnitAttr>(clause[side]))
              continue;
            const auto &application = array(clause[side]);
            auto found = relations.find(string(application[0]).str());
            if (found == relations.end())
              continue;
            const auto &selectors = array(application[1]);
            auto purposes = found->second.getPurposes();
            bool relevant = false;
            for (unsigned k = 0; k < selectors.size(); ++k)
              relevant |=
                  contractTerm(selectors[k]) == (*slot)[1] &&
                  mlir::cast<mlir::StringAttr>(purposes[k]).getValue() ==
                      string((*slot)[0]);
            if (!relevant)
              continue;
            std::set<std::string> roles;
            for (unsigned k = 0; k < selectors.size(); ++k) {
              if (mlir::cast<mlir::StringAttr>(purposes[k]).getValue() !=
                  "statement")
                continue;
              const auto &roster = callee.roles;
              auto formal = std::find(roster.begin(), roster.end(),
                                      string(array(selectors[k])[2]).str());
              if (formal == roster.end())
                return refuse("component-instantiation");
              roles.insert(
                  string(array(canonical[4])[formal - roster.begin()]).str());
            }
            allowed.push_back(std::move(roles));
          }
        }
        if (!source((*slot)[2], types[number(selector[1])], context, canonical,
                    allowed))
          return false;
      }
    }
    return true;
  }
  // Inspect every stored branch and callback, even when it is unreachable or
  // returns no seam value. This is an effect inventory, not a totality claim.
  bool deterministicBody(const SourceBlock &body, unsigned depth) {
    if (depth > 64)
      return refuse("component-seam-depth");
    for (const auto &instruction : body.instructions) {
      if (!charge())
        return false;
      auto *op = instruction.operation;
      auto tag = operationKind(op);
      if (!instruction.regions.empty() &&
          !mlir::isa<exec::TestOp, exec::RangeOp>(op))
        return refuse("component-seam-control");
      if (tag.starts_with("oracle_"))
        return refuse("component-seam-oracle");
      if (tag == "draw")
        return refuse("component-seam-sampling");
      if (tag == "exchange")
        return refuse("component-seam-message");
      if (tag == "protocol_apply" || tag == "protocol_repeat")
        return refuse("component-seam-effect");
      if (tag == "call" || tag == "local_call" ||
          mlir::isa<exec::ComputeOp>(op)) {
        if (!deterministicReference(symbol(op), depth + 1))
          return false;
      }
      if (mlir::isa<data::FiniteFoldOp, exec::FoldOp, exec::CollectOp>(op) &&
          !deterministicCallbacks(
              symbol(op, "domain"),
              symbol(op, mlir::isa<exec::CollectOp>(op) ? "body" : "step"),
              symbol(op, "predicate"), depth + 1))
        return false;
      for (const auto &region : instruction.regions)
        if (!deterministicBody(region, depth + 1))
          return false;
    }
    return true;
  }
  bool deterministicCallbacks(StringRef domain, StringRef body,
                              StringRef predicate, unsigned depth) {
    auto unit = mlir::cast<protocol_ir::ProtocolModuleOp>(
        program.native.get().getBody()->front());
    if (!mlir::dyn_cast_or_null<data::DomainOp>(
            mlir::SymbolTable::lookupSymbolIn(unit, domain)))
      return refuse("component-seam-call");
    return deterministicReference(body, depth) &&
           (predicate.empty() || deterministicReference(predicate, depth));
  }
  bool deterministicReference(StringRef name, unsigned depth) {
    if (depth > 64)
      return refuse("component-seam-depth");
    auto found = functions.find(name.str());
    return found != functions.end() ? deterministic(*found->second, depth)
                                    : refuse("component-seam-call");
  }
  bool deterministic(const SourceDefinition &function, unsigned depth) {
    if (depth > 64)
      return refuse("component-seam-depth");
    if (function.kind == "math")
      return true; // Whole-unit Math admission already excludes effects.
    if (function.kind != "local")
      return refuse("component-seam-effect");
    return deterministicBody(function.body, depth);
  }
};
} // namespace
Expected<json::Object> deriveComponentContracts(const SourceView &source) {
  Deriver derive(source);
  if (!derive.run() || derive.failure)
    return std::move(derive.failure);
  json::Value result = json::Object{{"proposals", std::move(derive.proposals)},
                                    {"seams", std::move(derive.rows)}};
  ownJsonStrings(result);
  return std::move(*result.getAsObject());
}
Error checkComponentContracts(const SourceView &source,
                              const json::Object &actual) {
  Deriver derive(source);
  if (!derive.run() || derive.failure || !derive.check(actual))
    return std::move(derive.failure);
  return Error::success();
}
} // namespace zkc::language
