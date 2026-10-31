#include "ComponentContracts.h"
#include "zkc/Contracts/SourceTerms.h"
#include "zkc/Support/Refusal.h"
#include <algorithm>
#include <functional>
#include <map>
#include <set>
using namespace llvm;
namespace zkc::language {
namespace {
using J = json::Value;
using A = json::Array;
const A &array(const J &value) { return *value.getAsArray(); }
StringRef string(const J &value) { return *value.getAsString(); }
unsigned number(const J &value) { return *value.getAsUINT64(); }
std::string key(const J &value) {
  std::string result;
  raw_string_ostream out(result);
  out << value;
  return result;
}
struct Flow {
  J route;
  std::set<std::string> pending;
  std::string effect;
  bool decision = false;
  unsigned nodes = 1;
  unsigned height = 1;
};
using Family = std::map<std::string, Flow>;
using Environment = std::vector<Family>;
struct Deriver {
  const A &snapshot;
  std::map<std::string, const A *> functions, contracts, sources;
  std::set<std::string> linear;
  struct CallContext {
    const A *caller;
    const A *callee;
    A visible;
  };
  std::map<std::pair<std::string, std::string>, CallContext> contexts;
  A rows, proposals;
  unsigned visits = 0;
  Error failure = Error::success();
  explicit Deriver(const J &value) : Deriver(array(value)) {}
  explicit Deriver(const A &value) : snapshot(value) {
    for (const auto &value : array(snapshot[7])) {
      const auto &definition = array(value);
      if (string(definition[0]) == "function")
        functions.emplace(string(definition[1]), &definition);
    }
    for (const auto &value : array(snapshot[8])) {
      const auto &contract = array(value);
      contracts.emplace(string(contract[0]), &array(contract[1]));
    }
    const auto &declarations = array(snapshot[10]);
    for (const auto &value : array(declarations[0])) {
      const auto &record = array(value);
      if (string(record[1]) == "linear")
        linear.insert(key(record[0]));
    }
    for (const auto &value : array(declarations[1])) {
      const auto &source = array(value);
      sources.emplace(string(source[0]), &source);
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
  bool pendingPort(const A &port) { return linear.count(key(port[1])); }
  Flow leaf(J route, bool pending = false) {
    auto keys =
        pending ? std::set<std::string>{key(route)} : std::set<std::string>{};
    return {std::move(route), std::move(keys), {}, false};
  }
  bool read(const Environment &environment, unsigned index, StringRef role,
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
  // The caller supplies a verified structured snapshot. Its execution
  // primitives have already passed the owning operation/binding admission.
  // That profile contains deterministic operations only; random services are
  // represented separately. The contract's spelling is not an operation name.
  bool purePrimitive(const A &descriptor) {
    if (descriptor.size() != 4 || descriptor[0] != J("exec") ||
        descriptor[1] != J("exec.apply"))
      return false;
    for (const auto &value : array(snapshot[6])) {
      const auto &binding = array(value);
      if (binding[1] == descriptor[2])
        return true;
    }
    return false;
  }
  bool consume(const std::vector<Flow> &flows, std::set<std::string> &live,
               bool method = false) {
    std::set<std::string> used;
    std::set<std::string> projections;
    for (const auto &flow : flows) {
      if (!pure(flow, method))
        return false;
      if (!flow.pending.empty() && !projections.insert(key(flow.route)).second)
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
    A routes;
    bool direct = true, method = false;
    for (const auto &flow : flows) {
      routes.push_back(flow.route);
      auto tag = string(array(flow.route)[0]);
      direct &= tag == "input" || tag == "result" || tag == "repeat_input" ||
                tag == "repeat_result";
      method |= !flow.effect.empty();
    }
    rows.push_back(A{caller.str(), std::move(endpoint),
                     explicitKind.empty() ? (method   ? "method"
                                             : direct ? "direct"
                                                      : "pure")
                                          : explicitKind.str(),
                     std::move(routes)});
  }
  // Classification belongs to the acceptance use, not to a representation
  // helper's flattened result type. Only conjunction preserves acceptance.
  J acceptance(const J &route) {
    const auto &parts = array(route);
    if (parts[0] != J("pure"))
      return route;
    auto tag = string(array(parts[1])[0]);
    if (tag == "local_call" || tag == "call") {
      A result(parts);
      result[0] = "terminal";
      return result;
    }
    if (tag == "bool.and") {
      A arguments;
      for (const auto &argument : array(parts[5]))
        arguments.push_back(acceptance(argument));
      A result(parts);
      result[5] = std::move(arguments);
      return result;
    }
    return route;
  }
  std::vector<std::string> roles(const A &function) {
    std::vector<std::string> result;
    for (const auto &role : array(array(function[6])[1]))
      result.push_back(string(role).str());
    return result;
  }
  bool makeInputs(const A &function, Environment &environment,
                  std::set<std::string> &live) {
    auto name = string(function[1]);
    const auto &types = array(function[4]);
    const auto &scopes = array(array(function[6])[2]);
    const A *source =
        sources.count(name.str()) ? sources.at(name.str()) : nullptr;
    for (unsigned i = 0; i < types.size(); ++i) {
      bool pending = false;
      if (source)
        for (const auto &value : array((*source)[1])) {
          const auto &port = array(value);
          if (number(port[3]) <= i && i < number(port[3]) + number(port[4]))
            pending = pendingPort(port);
        }
      Family family;
      for (const auto &role : array(scopes[i])) {
        auto flow = leaf(A{"input", i, role}, pending);
        live.insert(flow.pending.begin(), flow.pending.end());
        family.emplace(string(role), std::move(flow));
      }
      environment.push_back(std::move(family));
    }
    return true;
  }
  bool block(const A &function, const A &body, Environment environment,
             std::set<std::string> live, A path, std::vector<Family> &returned,
             unsigned depth = 0, A visible = {}) {
    if (depth > 64)
      return refuse("component-seam-depth");
    auto caller = string(function[1]);
    auto roster = roles(function);
    std::set<std::string> guarded;
    unsigned ordinal = 0;
    for (const auto &value : array(body[1])) {
      if (!charge())
        return false;
      const auto &instruction = array(value),
                 &descriptor = array(instruction[0]);
      auto tag = string(descriptor[0]), site = string(instruction[4]);
      const auto &args = array(instruction[1]), &types = array(instruction[2]);
      A position = path;
      position.push_back(ordinal++);
      std::vector<Family> results(types.size());
      if (tag == "protocol_apply") {
        auto found = functions.find(string(descriptor[1]).str());
        if (found == functions.end())
          return refuse("component-seam-call");
        const auto &callee = *found->second;
        auto childRoles = roles(callee);
        const auto &actualRoles = array(descriptor[2]);
        auto actual = [&](StringRef role) -> StringRef {
          size_t index =
              std::find(childRoles.begin(), childRoles.end(), role.str()) -
              childRoles.begin();
          return index < actualRoles.size() ? string(actualRoles[index])
                                            : StringRef();
        };
        auto source = sources.find(string(callee[1]).str());
        if (source != sources.end()) {
          unsigned portIndex = 0;
          for (const auto &value : array((*source->second)[1])) {
            const auto &port = array(value);
            if (pendingPort(port)) {
              std::vector<Flow> flows;
              for (unsigned i = 0; i < number(port[4]); ++i) {
                Flow flow{nullptr, {}, {}, false};
                if (!read(environment, number(args[number(port[3]) + i]),
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
        const auto &outputScopes = array(array(callee[6])[3]);
        for (unsigned i = 0; i < results.size(); ++i) {
          bool pending = false, decision = false;
          if (source != sources.end())
            for (const auto &value : array((*source->second)[2])) {
              const auto &port = array(value);
              if (number(port[3]) <= i && i < number(port[3]) + number(port[4]))
                pending = pendingPort(port);
            }
          for (const auto &value : *contracts.at(string(callee[1]).str())) {
            const auto &clause = array(value);
            if (!clause[4].getAsNull() && number(array(clause[4])[1]) == i)
              decision = true;
          }
          for (const auto &role : array(outputScopes[i])) {
            auto flow =
                leaf(A{"result", site.str(), i, actual(string(role)).str()},
                     pending);
            flow.decision =
                decision &&
                std::any_of(contracts.at(string(callee[1]).str())->begin(),
                            contracts.at(string(callee[1]).str())->end(),
                            [&](const J &value) {
                              const auto &clause = array(value);
                              return !clause[4].getAsNull() &&
                                     number(array(clause[4])[1]) == i &&
                                     array(clause[4])[2] == role;
                            });
            live.insert(flow.pending.begin(), flow.pending.end());
            results[i].emplace(actual(string(role)), std::move(flow));
          }
        }
        // Proposals are per actual call, even when the callee has no logical
        // slots.
        A slots;
        for (const auto &value : *contracts.at(string(callee[1]).str())) {
          const auto &clause = array(value);
          for (unsigned side : {2u, 3u}) {
            if (clause[side].getAsNull())
              continue;
            const auto &application = array(clause[side]);
            const A *relation = nullptr;
            for (const auto &value : array(snapshot[5]))
              if (array(value)[1] == application[0])
                relation = &array(value);
            if (!relation)
              return refuse("component-instantiation");
            const auto &selectors = array(application[1]),
                       &purposes = array((*relation)[9]);
            for (unsigned i = 0; i < selectors.size(); ++i) {
              if (string(purposes[i]) == "statement")
                continue;
              J slot = A{purposes[i], selectors[i], A{"open"}};
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
        proposals.push_back(A{caller.str(), site.str(), callee[1],
                              instruction[1], descriptor[2], std::move(slots)});
      } else if (tag == "protocol_repeat") {
        unsigned carried = number(descriptor[1]);
        if (array(instruction[3]).size() != 1)
          return refuse("component-seam-control");
        const auto &region = array(array(instruction[3])[0]);
        Environment inner;
        std::set<std::string> innerLive;
        std::vector<bool> marked(args.size(), false);
        std::vector<Flow> initialFlows;
        if (args.empty() || number(args[0]) >= environment.size())
          return refuse("component-seam-reference");
        Flow count{nullptr, {}, {}, false};
        for (const auto &[role, flow] : environment[number(args[0])])
          count.effect = joinEffect(count.effect, flow.effect);
        for (unsigned i = 0; i < args.size(); ++i) {
          Family family;
          if (number(args[i]) >= environment.size())
            return refuse("component-seam-reference");
          for (const auto &[role, flow] : environment[number(args[i])]) {
            bool pending = i > 0 && i <= carried && !flow.pending.empty();
            if (i > 0 && i <= carried)
              row(caller, A{"repeat_init", site.str(), i - 1, role}, {flow});
            if (pending) {
              initialFlows.push_back(flow);
              marked[i] = true;
            } else if (!flow.pending.empty())
              return refuse("component-seam-control");
            auto input = leaf(A{"repeat_input", site.str(), i, role}, pending);
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
        A nested = position;
        nested.push_back(0);
        unsigned carriedFlows = 0;
        for (unsigned i = 1; i <= carried; ++i)
          carriedFlows += inner[i].size();
        bool stable = false;
        // Reuse the actual traversal, discarding candidate rows until effects
        // close over every carried backedge. All candidate work is charged.
        for (unsigned pass = 0; pass <= 2 * carriedFlows; ++pass) {
          Deriver candidate(snapshot);
          candidate.visits = visits;
          candidate.contexts = contexts;
          yielded.clear();
          if (!candidate.block(function, array(region[2]), inner, innerLive,
                               nested, yielded, depth + 1, {})) {
            failure = std::move(candidate.failure);
            return false;
          }
          visits = candidate.visits;
          if (yielded.size() != carried)
            return refuse("component-seam-control");
          stable = true;
          for (unsigned i = 0; i < carried; ++i)
            for (auto &[role, input] : inner[i + 1]) {
              Flow output{nullptr, {}, {}, false};
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
          for (const auto &[role, flow] : environment[number(args[i])]) {
            std::vector<Flow> dependencies{flow};
            if (i > 0)
              for (const auto &[_, control] : environment[number(args[0])])
                dependencies.push_back(control);
            if (i > 0 && i <= carried) {
              Flow output{nullptr, {}, {}, false};
              if (!read(yielded, i - 1, role, output))
                return false;
              dependencies.push_back(std::move(output));
            }
            row(caller, A{"repeat_input", site.str(), i, role}, dependencies);
          }
        for (unsigned i = 0; i < carried; ++i)
          for (const auto &role : array(array(descriptor[4])[i])) {
            auto found = yielded[i].find(string(role).str());
            if (found == yielded[i].end())
              return refuse("component-seam-role");
            Flow initial{nullptr, {}, {}, false};
            if (!read(environment, number(args[i + 1]), string(role), initial))
              return false;
            auto controlled = found->second;
            controlled.effect = joinEffect(controlled.effect, count.effect);
            row(caller, A{"yield", site.str(), i, role}, {controlled});
            // Both alternatives are retained: zero iterations returns initial
            // state. The matching repeat_input row also retains count control.
            row(caller, A{"repeat_result", site.str(), i, role},
                {initial, controlled});
            auto flow =
                leaf(A{"repeat_result", site.str(), i, role}, marked[i + 1]);
            flow.effect = joinEffect(joinEffect(initial.effect, count.effect),
                                     found->second.effect);
            live.insert(flow.pending.begin(), flow.pending.end());
            results[i].emplace(string(role), std::move(flow));
          }
      } else {
        // Logical oracle routes need anchor-aware seams. Do not classify a new
        // oracle instruction as a pure value merely because its descriptor is
        // outside the old effect cases. Export and seam admission are separate.
        if (tag.starts_with("oracle_"))
          return refuse("component-seam-oracle");
        if (!array(instruction[3]).empty())
          return refuse("component-seam-control");
        if (tag == "statement")
          continue;
        if (tag == "guard") {
          Flow flow{nullptr, {}, {}, false};
          if (!read(environment, number(args[0]), string(descriptor[1]), flow))
            return false;
          if (!flow.pending.empty()) {
            row(caller, A{"guard", site.str(), descriptor[1]}, {flow},
                "method");
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
        for (const auto &role : roster) {
          if (tag == "restrict" &&
              std::none_of(
                  array(descriptor[1]).begin(), array(descriptor[1]).end(),
                  [&](const J &value) { return string(value) == role; }))
            continue;
          if ((tag == "local_call" || tag == "draw") &&
              string(descriptor[tag == "draw" ? 1 : 2]) != role)
            continue;
          if (tag == "exchange" && string(descriptor[2]) != role)
            continue;
          std::vector<Flow> operands;
          bool available = true;
          for (const auto &argument : args) {
            unsigned index = number(argument);
            if (index >= environment.size())
              return refuse("component-seam-reference");
            auto sourceRole =
                tag == "exchange" ? string(descriptor[1]).str() : role;
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
          A routes;
          Flow aggregate{nullptr, {}, {}, false};
          for (const auto &operand : operands) {
            routes.push_back(operand.route);
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
          } else if ((tag == "exec" && !purePrimitive(descriptor)) ||
                     tag == "apply" || tag == "fold")
            aggregate.effect =
                tag == "exec" && string(descriptor[1]).starts_with("oracle.")
                    ? "component-seam-oracle"
                    : "component-seam-effect";
          else if (tag == "call" || tag == "local_call") {
            auto found = functions.find(string(descriptor[1]).str());
            if (found == functions.end())
              return refuse("component-seam-call");
            if (tag == "call" && string((*found->second)[2]) != "math")
              aggregate.effect = "component-seam-effect";
            if (tag == "local_call" && !deterministic(*found->second, 0))
              return false;
          }
          for (unsigned i = 0; i < types.size(); ++i) {
            auto flow = aggregate;
            flow.route =
                tag == "restrict"
                    ? operands[0].route
                    : J(A{tag == "draw" || tag == "exchange" ? "action"
                                                             : "pure",
                          instruction[0], A(position), i, role, A(routes)});
            if (tag == "local_call" && aggregate.pending.empty() &&
                aggregate.effect.empty())
              flow.route = A{"result", site.str(), i, role};
            // Every output projection of a Local representation map must
            // subsequently be covered, even when it shares input ancestry.
            if (tag == "local_call" && !aggregate.pending.empty()) {
              auto projection = key(flow.route);
              flow.pending.insert(projection);
              live.insert(std::move(projection));
            }
            flow.decision = (tag == "local_call" || tag == "call") &&
                            array(types[i]) == A{"apply", "bool", A{}};
            if (tag == "bool.and")
              flow.decision =
                  (operands[0].decision || operands[0].pending.empty()) &&
                  (operands[1].decision || operands[1].pending.empty());
            results[i].emplace(role, std::move(flow));
          }
        }
      }
      A scopes;
      for (const auto &family : results) {
        A roles;
        for (const auto &[role, _] : family)
          roles.push_back(role);
        scopes.push_back(std::move(roles));
      }
      visible.push_back(A{site.str(), instruction[2], std::move(scopes)});
      environment.insert(environment.begin(), results.begin(), results.end());
    }
    const auto &terminal = array(body[2]);
    auto tag = string(terminal[0]);
    if (tag == "stop") {
      returned.clear();
      return true;
    }
    if (tag != "return" && tag != "yield")
      return refuse("component-seam-control");
    for (const auto &value : array(terminal[1])) {
      if (number(value) >= environment.size())
        return refuse("component-seam-reference");
      returned.push_back(environment[number(value)]);
    }
    if (tag == "yield") {
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
        for (const auto &value : array((*source->second)[2])) {
          const auto &port = array(value);
          if (pendingPort(port)) {
            std::vector<Flow> flows;
            for (unsigned i = 0; i < number(port[4]); ++i) {
              Flow flow{nullptr, {}, {}, false};
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
      for (const auto &value : *contracts.at(caller.str())) {
        const auto &clause = array(value);
        if (!clause[4].getAsNull()) {
          const auto &decision = array(clause[4]);
          Flow flow{nullptr, {}, {}, false};
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
            flow.route = acceptance(flow.route);
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
    // Anchor contracts require the oracle-store interpretation. Refuse them
    // before any data-only slot traversal; a data ABI cannot resolve an anchor.
    for (const auto &[name, clauses] : contracts)
      for (const auto &value : *clauses) {
        const auto &clause = array(value);
        for (unsigned side : {2u, 3u}) {
          if (clause[side].getAsNull())
            continue;
          for (const auto &value : array(array(clause[side])[1])) {
            if (!charge())
              return false;
            if (array(value)[0] == J("anchor"))
              return refuse("component-seam-oracle");
          }
        }
      }

    if (linear.empty())
      return true;
    std::map<std::string, J> meanings;
    for (const auto &[name, source] : sources) {
      for (unsigned side : {1u, 2u})
        for (const auto &value : array((*source)[side])) {
          const auto &port = array(value);
          if (!pendingPort(port))
            continue;
          if (array(port[2]).size() != 1 || !number(port[4]))
            return refuse("component-claim-role");
          // The selected protocol may be a library root with linear ports.
          // Concrete Entry target/acceptance checks belong to claim selection.
          // Clause-free wrappers assert no relation; their resource ownership
          // is still checked by the traversal below.
          if (contracts.at(name)->empty())
            continue;
          std::set<std::string> relations;
          for (const auto &value : *contracts.at(name)) {
            const auto &clause = array(value);
            for (unsigned part : {2u, 3u}) {
              if (clause[part].getAsNull())
                continue;
              const auto &application = array(clause[part]);
              for (const auto &value : array(application[1])) {
                const auto &selector = array(value);
                if (selector[0] == J(side == 1 ? "input" : "output") &&
                    number(port[3]) <= number(selector[1]) &&
                    number(selector[1]) < number(port[3]) + number(port[4]))
                  relations.insert(string(application[0]).str());
              }
            }
          }
          if (relations.size() != 1)
            return refuse("component-claim-relation");
          auto [previous, added] =
              meanings.emplace(key(port[1]), *relations.begin());
          if (!added && previous->second != J(*relations.begin()))
            return refuse("component-claim-relation");
        }
    }
    for (const auto &[name, function] : functions) {
      if (string((*function)[2]) != "protocol")
        continue;
      Environment inputs;
      std::set<std::string> live;
      std::vector<Family> returned;
      if (!makeInputs(*function, inputs, live) ||
          !block(*function, array((*function)[9]), std::move(inputs),
                 std::move(live), {}, returned))
        return false;
    }
    return true;
  }
  bool logicalSlot(const A &owner, StringRef purpose, const J &selector) {
    for (const auto &value : *contracts.at(string(owner[1]).str())) {
      const auto &clause = array(value);
      for (unsigned side : {2u, 3u}) {
        if (clause[side].getAsNull())
          continue;
        const auto &application = array(clause[side]);
        for (const auto &relation : array(snapshot[5])) {
          if (array(relation)[1] != application[0])
            continue;
          const auto &selectors = array(application[1]),
                     &purposes = array(array(relation)[9]);
          for (unsigned i = 0; i < selectors.size(); ++i)
            if (selectors[i] == selector && string(purposes[i]) == purpose)
              return true;
        }
      }
    }
    return false;
  }
  bool source(const J &value, const J &expected, const CallContext &context,
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
    auto index = [&](const J &value, const A &types) {
      auto number = value.getAsUINT64();
      return number && *number < types.size() && types[*number] == expected;
    };
    if (tag == "open")
      return (items.size() == 1 && depth == 0) ||
             refuse("component-instantiation");
    if (tag == "operand" && items.size() == 3 && items[1].getAsUINT64() &&
        items[2].getAsString()) {
      const auto &callee = *context.callee, &interface = array(callee[6]);
      if (!index(items[1], array(callee[4])) || !permit(string(items[2])))
        return refuse("component-instantiation");
      for (const auto &role : array(array(interface[2])[number(items[1])])) {
        const auto &roles = array(interface[1]);
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
      if (!index((*selected)[1], array(owner[4])) ||
          !permit(string((*selected)[2])) || !logicalSlot(owner, tag, items[1]))
        return refuse("component-instantiation");
      const auto &scope =
          array(array(array(owner[6])[2])[number((*selected)[1])]);
      return std::find(scope.begin(), scope.end(), (*selected)[2]) !=
                 scope.end() ||
             refuse("component-instantiation");
    }
    if (tag == "result" && items.size() == 4 && items[1].getAsString() &&
        items[2].getAsUINT64() && items[3].getAsString()) {
      const A *selected = nullptr;
      for (const auto &value : context.visible)
        if (array(value)[0] == items[1]) {
          if (selected)
            return refuse("component-instantiation");
          selected = &array(value);
        }
      if (!selected || !index(items[2], array((*selected)[1])) ||
          !permit(string(items[3])))
        return refuse("component-instantiation");
      const auto &scope = array(array((*selected)[2])[number(items[2])]);
      return std::find(scope.begin(), scope.end(), items[3]) != scope.end() ||
             refuse("component-instantiation");
    }
    if (tag == "math" && items.size() == 4 && items[1].getAsString() &&
        items[2].getAsUINT64() && items[3].getAsArray()) {
      auto found = functions.find(string(items[1]).str());
      if (found == functions.end())
        return refuse("component-instantiation");
      const auto &helper = *found->second;
      if (helper[2] != J("math") || !index(items[2], array(helper[5])) ||
          array(items[3]).size() != array(helper[4]).size())
        return refuse("component-instantiation");
      for (unsigned i = 0; i < array(items[3]).size(); ++i)
        if (!source(array(items[3])[i], array(helper[4])[i], context, proposal,
                    allowed, depth + 1))
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
      const auto &interface = array(callee[6]);
      for (unsigned j = 0; j < slots->size(); ++j) {
        auto slot = (*slots)[j].getAsArray();
        const auto &expectedSlot = array(array(canonical[5])[j]);
        if (!slot || slot->size() != 3 || (*slot)[0] != expectedSlot[0] ||
            (*slot)[1] != expectedSlot[1])
          return refuse("component-instantiation");
        const auto &selector = array((*slot)[1]);
        const auto &types = array(callee[selector[0] == J("input") ? 4 : 5]);
        std::vector<std::set<std::string>> allowed;
        for (const auto &value : *contracts.at(string(callee[1]).str())) {
          const auto &clause = array(value);
          for (unsigned side : {2u, 3u}) {
            if (clause[side].getAsNull())
              continue;
            const auto &application = array(clause[side]);
            for (const auto &relation : array(snapshot[5])) {
              if (array(relation)[1] != application[0])
                continue;
              const auto &selectors = array(application[1]),
                         &purposes = array(array(relation)[9]);
              bool relevant = false;
              for (unsigned k = 0; k < selectors.size(); ++k)
                relevant |=
                    selectors[k] == (*slot)[1] && purposes[k] == (*slot)[0];
              if (!relevant)
                continue;
              std::set<std::string> roles;
              for (unsigned k = 0; k < selectors.size(); ++k) {
                if (purposes[k] != J("statement"))
                  continue;
                const auto &roster = array(interface[1]);
                auto formal = std::find(roster.begin(), roster.end(),
                                        array(selectors[k])[2]);
                if (formal == roster.end())
                  return refuse("component-instantiation");
                roles.insert(
                    string(array(canonical[4])[formal - roster.begin()]).str());
              }
              allowed.push_back(std::move(roles));
            }
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
  bool deterministicBody(const A &body, unsigned depth) {
    if (depth > 64)
      return refuse("component-seam-depth");
    for (const auto &value : array(body[1])) {
      if (!charge())
        return false;
      const auto &instruction = array(value),
                 &descriptor = array(instruction[0]);
      auto tag = string(descriptor[0]);
      const auto &regions = array(instruction[3]);
      if (!regions.empty() && tag != "if" && tag != "for" &&
          tag != "for_condition")
        return refuse("component-seam-control");
      if (tag.starts_with("oracle_"))
        return refuse("component-seam-oracle");
      if (tag == "draw")
        return refuse("component-seam-sampling");
      if (tag == "exchange")
        return refuse("component-seam-message");
      if ((tag == "exec" && !purePrimitive(descriptor)) ||
          tag == "protocol_apply" || tag == "protocol_repeat")
        return refuse(tag == "exec" &&
                              string(descriptor[1]).starts_with("oracle.")
                          ? "component-seam-oracle"
                          : "component-seam-effect");
      if (tag == "call" || tag == "local_call" || tag == "apply") {
        if (!deterministicReference(string(descriptor[1]), depth + 1,
                                    tag == "apply"))
          return false;
      }
      if (tag == "fold" &&
          !deterministicCallbacks(string(descriptor[1]), string(descriptor[2]),
                                  string(descriptor[3]), depth + 1))
        return false;
      for (const auto &region : regions)
        if (!deterministicBody(array(array(region)[2]), depth + 1))
          return false;
    }
    return true;
  }
  bool deterministicCallbacks(StringRef domain, StringRef body,
                              StringRef predicate, unsigned depth) {
    if (std::none_of(
            array(snapshot[4]).begin(), array(snapshot[4]).end(),
            [&](const J &value) { return array(value)[1] == J(domain); }))
      return refuse("component-seam-call");
    return deterministicReference(body, depth, false) &&
           (predicate.empty() ||
            deterministicReference(predicate, depth, false));
  }
  bool deterministicReference(StringRef name, unsigned depth,
                              bool computation) {
    if (depth > 64)
      return refuse("component-seam-depth");
    auto found = functions.find(name.str());
    if (found != functions.end())
      return deterministic(*found->second, depth);
    if (computation)
      for (const auto &value : array(snapshot[7])) {
        const auto &declaration = array(value);
        if (declaration[1] != J(name))
          continue;
        auto tag = string(declaration[0]);
        if (tag == "realize" || tag == "map")
          return deterministicReference(string(declaration[4]), depth, false);
        if (tag == "finite" || tag == "collect")
          return deterministicCallbacks(string(declaration[5]),
                                        string(declaration[6]),
                                        string(declaration[7]), depth);
      }
    return refuse("component-seam-call");
  }
  bool deterministic(const A &function, unsigned depth) {
    if (depth > 64)
      return refuse("component-seam-depth");
    if (function[2] == J("math"))
      return true; // Whole-unit Math admission already excludes effects.
    if (function[2] != J("local"))
      return refuse("component-seam-effect");
    return deterministicBody(array(function[9]), depth);
  }
};
} // namespace
Expected<json::Object> deriveComponentContracts(const J &snapshot) {
  Deriver derive(snapshot);
  if (!derive.run())
    return std::move(derive.failure);
  return json::Object{{"proposals", std::move(derive.proposals)},
                      {"seams", std::move(derive.rows)}};
}
Error checkComponentContracts(const J &snapshot, const json::Object &actual) {
  Deriver derive(snapshot);
  if (!derive.run() || !derive.check(actual))
    return std::move(derive.failure);
  return Error::success();
}
Error checkComponentDeclarations(const J &value) {
  auto rows = value.getAsArray();
  if (!rows || rows->size() != 2 || !(*rows)[0].getAsArray() ||
      !(*rows)[1].getAsArray())
    return error("component-declaration");
  auto validString = [](const J &value) {
    auto text = value.getAsString();
    return text && !text->empty() && text->size() <= 512 &&
           json::isUTF8(*text) && !text->contains('\0');
  };
  unsigned remaining = 1048576;
  std::function<bool(const J &, unsigned)> bounded = [&](const J &value,
                                                         unsigned depth) {
    if (!remaining || depth > 128)
      return false;
    --remaining;
    if (const auto *items = value.getAsArray())
      for (const auto &item : *items)
        if (!bounded(item, depth + 1))
          return false;
    return true;
  };
  if (!bounded(value, 0))
    return error("component-declaration-limit");
  std::set<std::string> types, owners;
  std::map<std::string, StringRef> nominalKinds;
  std::map<std::string, const A *> declarations;
  auto fields = [&](const A &members) -> Error {
    if (members.size() > 512)
      return error("component-declaration-limit");
    std::set<std::string> names;
    for (const auto &value : members) {
      auto field = value.getAsArray();
      if (!field || field->size() != 2 || !validString((*field)[0]))
        return error("component-declaration");
      if (!names.insert(string((*field)[0]).str()).second)
        return error("component-declaration-duplicate");
      if (auto e = checkStaticTerm((*field)[1]))
        return e;
    }
    return Error::success();
  };
  if (array((*rows)[0]).size() > 128 || array((*rows)[1]).size() > 128)
    return error("component-declaration-limit");
  for (const auto &value : array((*rows)[0])) {
    auto record = value.getAsArray();
    if (!record || record->size() != 4 || !(*record)[1].getAsString() ||
        !(*record)[2].getAsBoolean() || !(*record)[3].getAsArray())
      return error("component-declaration");
    if (auto e = checkStaticTerm((*record)[0]))
      return e;
    auto type = (*record)[0].getAsArray();
    if (!type || type->size() != 4 || (*type)[0] != J("nominal") ||
        ((*type)[1] != J("record") && (*type)[1] != J("logical_record") &&
         (*type)[1] != J("variant")))
      return error("component-declaration-record");
    auto kind = string((*type)[1]);
    auto [nominal, added] =
        nominalKinds.emplace(string((*type)[2]).str(), kind);
    if (!added && nominal->second != kind)
      return error("component-declaration-record");
    if (!types.insert(key((*record)[0])).second)
      return error("component-declaration-duplicate");
    declarations.emplace(key((*record)[0]), record);
    auto resource = string((*record)[1]);
    if (resource != "ordinary" && resource != "affine" && resource != "linear")
      return error("component-declaration");
    if (kind == "logical_record" && resource != "ordinary")
      return error("component-declaration-record");
    if (resource == "linear" && !*(*record)[2].getAsBoolean())
      return error("component-declaration-record");
    if (array((*record)[3]).size() > 512)
      return error("component-declaration-limit");
    if (kind != "variant") {
      if (auto e = fields(array((*record)[3])))
        return e;
      continue;
    }
    std::set<std::string> alternatives;
    for (const auto &value : array((*record)[3])) {
      auto alternative = value.getAsArray();
      if (!alternative || alternative->size() != 2 ||
          !validString((*alternative)[0]) || !(*alternative)[1].getAsArray())
        return error("component-declaration");
      if (!alternatives.insert(string((*alternative)[0]).str()).second)
        return error("component-declaration-duplicate");
      if (auto e = fields(array((*alternative)[1])))
        return e;
    }
  }
  // Logical records cannot acquire resource custody through an ordinary
  // nominal child, including children erased by zero-length layouts.
  std::set<std::string> ordinary;
  std::function<Error(const J &, unsigned)> shared =
      [&](const J &value, unsigned depth) -> Error {
    if (!remaining || depth > 64)
      return error("component-declaration-limit");
    --remaining;
    const auto &term = array(value);
    auto tag = string(term[0]);
    const A *arguments = nullptr;
    if (tag == "nominal") {
      auto kind = string(term[1]);
      if (kind == "logical_record")
        return error("component-declaration-record");
      if (kind == "record" || kind == "variant") {
        auto identity = key(value);
        auto found = declarations.find(identity);
        if (found == declarations.end() || (*found->second)[1] != J("ordinary"))
          return error("component-declaration-record");
        if (!ordinary.insert(identity).second)
          return Error::success();
        const auto &members = array((*found->second)[3]);
        if (kind == "variant") {
          for (const auto &alternative : members)
            for (const auto &field : array(array(alternative)[1]))
              if (auto e = shared(array(field)[1], depth + 1))
                return e;
        } else
          for (const auto &field : members)
            if (auto e = shared(array(field)[1], depth + 1))
              return e;
        // Closed member types already substitute the nominal arguments.
        // A phantom type argument does not confer resource custody.
        return Error::success();
      }
      arguments = &array(term[3]);
    } else if (tag == "array") {
      return shared(term[1], depth + 1);
    } else if (tag == "tuple")
      arguments = &array(term[1]);
    else if (tag == "builtin" || tag == "formal")
      arguments = &array(term[2]);
    if (arguments)
      for (const auto &argument : *arguments)
        if (auto e = shared(argument, depth + 1))
          return e;
    return Error::success();
  };
  for (const auto &[identity, declaration] : declarations)
    if (array((*declaration)[0])[1] == J("logical_record"))
      for (const auto &field : array((*declaration)[3]))
        if (auto e = shared(array(field)[1], 0))
          return e;
  for (const auto &value : array((*rows)[1])) {
    auto owner = value.getAsArray();
    if (!owner || owner->size() != 3 || !validString((*owner)[0]))
      return error("component-declaration");
    if (!owners.insert(string((*owner)[0]).str()).second)
      return error("component-declaration-duplicate");
    for (unsigned side : {1u, 2u}) {
      auto ports = (*owner)[side].getAsArray();
      if (!ports || ports->size() > 512)
        return error("component-declaration");
      std::set<std::string> names;
      for (const auto &value : *ports) {
        auto port = value.getAsArray();
        if (!port || port->size() != 5 || !validString((*port)[0]) ||
            !(*port)[2].getAsArray() || !(*port)[3].getAsUINT64() ||
            !(*port)[4].getAsUINT64() || *(*port)[3].getAsUINT64() > 512 ||
            *(*port)[4].getAsUINT64() > 512)
          return error("component-declaration");
        if (!names.insert(string((*port)[0]).str()).second)
          return error("component-declaration-duplicate");
        if (auto e = checkStaticTerm((*port)[1]))
          return e;
        if (array((*port)[2]).size() > 16)
          return error("component-declaration-limit");
        std::set<std::string> roles;
        for (const auto &role : array((*port)[2])) {
          if (!validString(role))
            return error("component-declaration-role");
          if (!roles.insert(string(role).str()).second)
            return error("component-declaration-role");
        }
      }
    }
  }
  return Error::success();
}
} // namespace zkc::language
