#include "zkc/Program/Admission.h"
#include "EncodingLimits.h"
#include "Structure.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/NativePolicy.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Program/Codec.h"
#include "llvm/ADT/StringExtras.h"
#include <set>

using namespace llvm;
namespace zkc::protocol {
namespace {
struct Port {
  std::string type;
  bool operator==(const Port &p) const { return type == p.type; }
};
struct Definition {
  std::vector<Port> inputs, outputs;
  const program::Body *body = nullptr;
  bool realization = false;
  program::Names arguments;
  std::string instance, role;
  std::map<std::string, std::string> services;
};
bool identifier(StringRef s, size_t limit = 128) {
  return !s.empty() && s.size() <= limit &&
         (isAlpha(s.front()) || s.front() == '_') && all_of(s, [](char c) {
           return isAlnum(c) || c == '_' || c == '.' || c == '-';
         });
}
bool naturalString(StringRef s, uint64_t max) {
  uint64_t n = 0;
  return !s.empty() && (s.size() == 1 || s.front() != '0') &&
         all_of(s, [](char c) { return c >= '0' && c <= '9'; }) &&
         !s.getAsInteger(10, n) && n <= max;
}
class Admission {
  std::string problem;
  std::map<std::string, protocol::OperationBinding> bindings;
  bool target = false, physical = false;
  size_t instructions = 0;
  std::map<std::string, Definition> functions, participants;
  std::map<std::string, std::set<std::string>> edges;
  std::set<std::string> symbols;
  std::set<std::pair<std::string, std::string>> participantIdentities;
  std::map<std::pair<std::string, std::string>, std::string> schemas;

  bool schema(StringRef scope, StringRef name, StringRef type) {
    auto [it, inserted] =
        schemas.emplace(std::make_pair(scope.str(), name.str()), type.str());
    return inserted || it->second == type || fail("interactive-schema-type");
  }

  bool fail(StringRef code) {
    if (problem.empty()) {
      problem = code.str();
    }
    return false;
  }
  bool name(StringRef value) {
    return identifier(value) || fail("interactive-name");
  }
  bool natural(StringRef value, uint64_t limit, StringRef limitReason) {
    if (value.empty() ||
        !all_of(value, [](char c) { return c >= '0' && c <= '9'; }))
      return fail("expected-natural");
    if (value.size() > 1 && value.front() == '0')
      return fail("noncanonical-natural");
    return naturalString(value, limit) || fail(limitReason);
  }
  bool wireType(StringRef spelling) {
    if (serializable(spelling))
      return true;
    auto parsed = parseBoundType(spelling, physical);
    if (!parsed) {
      consumeError(parsed.takeError());
      return false;
    }
    return nativeFieldArrayWire(*parsed, physical) || nativeDataFrame(*parsed);
  }
  bool type(StringRef s) {
    auto parsed = parseBoundType(s, physical);
    if (!parsed) {
      consumeError(parsed.takeError());
      return fail("binding-type");
    }
    if (isDiagonalRepresentation(parsed->representation))
      return fail("binding-representation");
    return true;
  }

  bool pairs(const protocol::Assignments &values,
             std::map<std::string, std::string> &out) {
    for (const auto &[key, value] : values)
      if (!name(key) || !name(value) || !out.emplace(key, value).second)
        return fail("interactive-binding");
    return true;
  }
  bool input(StringRef nameValue, StringRef spelling, Definition &def) {
    if (!name(nameValue) || is_contained(def.arguments, nameValue.str()))
      return fail("interactive-argument");
    if (!type(spelling))
      return fail("interactive-port-role");
    def.arguments.push_back(nameValue.str());
    def.inputs.push_back({spelling.str()});
    return true;
  }
  bool output(StringRef spelling, Definition &def) {
    if (!type(spelling))
      return fail("interactive-port-role");
    def.outputs.push_back({spelling.str()});
    return true;
  }
  bool localPorts(const std::vector<program::Parameter> &arguments,
                  const program::Names &results, Definition &def) {
    if (arguments.size() > 1024 || results.size() > 1024)
      return fail("interactive-ports");
    for (const auto &arg : arguments)
      if (!input(arg.name, arg.type, def))
        return false;
    for (const auto &result : results)
      if (!output(result, def))
        return false;
    return true;
  }
  bool symbol(StringRef value) {
    return name(value) && (symbols.insert(value.str()).second ||
                           fail("interactive-duplicate-symbol"));
  }
  bool declare(const program::Function &f) {
    if (!symbol(f.name))
      return false;
    Definition d;

    d.body = &f.body;
    {
      if (!f.origin || !name(f.origin->definition) ||
          f.origin->arguments.size() > 128)
        return fail("binding-logical-origin");
      std::set<std::string> parameters;
      for (const auto &[key, value] : f.origin->arguments)
        if (!name(key) || !parameters.insert(key).second ||
            (installedIdentitySort(value).empty() &&
             !staticIdentityMatches("Nat", value) &&
             !staticIdentityMatches("Type", value)))
          return fail("binding-logical-origin");
    }
    if (!localPorts(f.arguments, f.results, d))
      return false;
    functions.emplace(f.name, std::move(d));
    return true;
  }
  bool declare(const program::Participant &p) {
    // Internal local-definition admission never reaches participant
    // declarations.
    auto invalidBoundary = [&](StringRef spelling) {
      auto type = parseBoundType(spelling, physical);
      if (!type) {
        consumeError(type.takeError());
        // Ordinary port admission below owns type-formation diagnostics.
        return false;
      }
      return !programPort(*type);
    };
    for (const auto &a : p.arguments)
      if (invalidBoundary(a.type))
        return fail("variant-boundary");
    for (const auto &t : p.results)
      if (invalidBoundary(t))
        return fail("variant-boundary");
    if (!symbol(p.name) || !name(p.instance) || !name(p.role))
      return false;
    Definition d;

    d.body = &p.body;
    d.instance = p.instance;
    d.role = p.role;
    if (p.services.size() + p.arguments.size() > 1024)
      return fail("interactive-port-limit");
    std::set<uint64_t> serviceIndices;
    std::set<std::string> portNames;
    for (const auto &arg : p.arguments)
      portNames.insert(arg.name);
    for (const auto &port : p.services) {
      if (!name(port.name) || randomServiceField(port.contract).empty() ||
          !portNames.insert(port.name).second ||
          !serviceIndices.insert(port.inputIndex).second ||
          port.inputIndex >= p.arguments.size() + p.services.size())
        return fail("service-port-interface");
      d.services.emplace(port.name, port.contract);
    }
    if (!participantIdentities.emplace(p.instance, p.role).second)
      return fail("interactive-participant-identity");
    if (!localPorts(p.arguments, p.results, d))
      return false;
    participants.emplace(p.name, std::move(d));
    return true;
  }
  using Env = std::map<std::string, Port>;
  bool bind(const program::Names &outputs, const std::vector<Port> &ports,
            Env &env) {
    if (outputs.size() != ports.size())
      return fail("interactive-shape");
    for (size_t i = 0; i < outputs.size(); ++i)
      if (!name(outputs[i]) || !env.emplace(outputs[i], ports[i]).second)
        return fail("interactive-ssa");
    return true;
  }
  bool operands(const program::Names &values, const Env &env,
                std::vector<Port> &ports, std::set<std::string> &consumed) {
    for (const auto &value : values) {
      auto p = env.find(value);
      if (p == env.end())
        return fail("interactive-unavailable");
      if (consumed.count(p->first) ||
          (!duplicable(p->second.type) && !consumed.insert(p->first).second))
        return fail("interactive-resource-reuse");
      ports.push_back(p->second);
    }
    return true;
  }
  bool callsMatchUnsafe(const std::string &callee,
                        std::set<std::string> &seen) {
    if (!seen.insert(callee).second)
      return false;
    auto found = functions.find(callee);
    if (found == functions.end() || !found->second.body)
      return false;
    bool result = false;
    program::walk(*found->second.body, [&](const program::Instruction &i) {
      if (const auto *op = i.get<program::Operation>()) {
        auto binding = bindings.find(op->callee);
        result |= binding != bindings.end() &&
                  isHistoryTransition(binding->second.application.contract);
      } else if (const auto *call = i.get<program::LocalApply>())
        result |= callsMatchUnsafe(call->callee, seen);
    });
    return result;
  }
  bool body(const program::Body &instructionsBody, Env env,
            const std::vector<Port> &returns, const Definition &def,
            StringRef owner, bool local, std::set<std::string> &sites,
            unsigned depth = 0, bool loop = false,
            std::vector<Port> *inferredReturns = nullptr,
            bool inMatch = false) {
    if (instructionsBody.empty() || depth > 64)
      return fail("interactive-body");
    std::set<std::string> consumed;
    std::set<std::string> diagonalUses;
    for (const auto &instruction : instructionsBody) {
      if (target && !local) {
        if (instruction.get<program::Stop>())
          return fail("native-participant-terminal");
      }
      if (++instructions > 32768)
        return fail("interactive-instruction-limit");
      if (instruction.isTerminator() !=
          (&instruction == &instructionsBody.back()))
        return fail("interactive-terminator");
      if (const auto *release = instruction.get<program::Release>()) {
        if (!physical || !local || !instruction.site.empty())
          return fail("interactive-release-context");
        if (release->values.size() > 1024)
          return fail("interactive-port-limit");
        if (release->values.empty())
          return fail("interactive-release-empty");
        for (const auto &value : release->values) {
          auto found = env.find(value);
          if (found == env.end() || !consumed.insert(value).second)
            return fail("interactive-release-unavailable");
          if (!discardable(found->second.type))
            return fail("interactive-release-resource");
        }
        continue;
      }
      const auto *ret = instruction.get<program::Return>();
      const auto *yield = instruction.get<program::Yield>();
      if (ret || yield) {
        std::vector<Port> values;
        if (bool(yield) != loop)
          return fail(local ? "local-terminal-context" : "interactive-return");
        if (!operands(ret ? ret->values : yield->values, env, values, consumed))
          return false;
        if (!inferredReturns && values != returns)
          return fail(
              local ? (loop ? "local-yield-types" : "function-return-types")
                    : "interactive-return");
        if (inferredReturns)
          *inferredReturns = values;
        continue;
      }
      // Service names share the participant value namespace, while remaining
      // unavailable as data operands.
      for (const auto &[service, contract] : def.services)
        if (env.count(service))
          return fail("service-port-interface");
      if (!name(instruction.site) || !sites.insert(instruction.site).second)
        return fail("interactive-site");
      if (const auto *query = instruction.get<program::ServiceQuery>()) {
        if (local || !target || !def.services.count(query->port))
          return fail("service-query-context");
        auto method =
            serviceMethod(def.services.at(query->port), query->method);
        if (!method || query->inputs.size() != method->inputs.size())
          return fail("service-query-signature");
        auto port = [&](StringRef spelling) -> std::optional<Port> {
          auto logical = parseBoundType(spelling, false);
          if (!logical) {
            consumeError(logical.takeError());
            return {};
          }
          if (physical) {
            auto selected = defaultRepresentation(*logical);
            if (!selected) {
              consumeError(selected.takeError());
              return {};
            }
            logical = std::move(selected);
          }
          return Port{logical->spelling()};
        };
        std::vector<Port> inputs, expected;
        for (const auto &spelling : method->inputs) {
          auto p = port(spelling);
          if (!p)
            return fail("service-query-signature");
          expected.push_back(*p);
        }
        auto output = port(method->output);
        if (!output)
          return fail("service-query-signature");
        if (!operands(query->inputs, env, inputs, consumed))
          return false;
        if (inputs != expected)
          return fail("service-query-signature");
        if (!bind(query->outputs, {*output}, env))
          return false;
      } else if (const auto *literal =
                     instruction.get<program::BooleanConstant>()) {
        if (!local)
          return fail("native-boolean-context");
        if (!bind({literal->output},
                  {{physical ? "bool@native.bool/0" : "bool"}}, env))
          return false;
      } else if (const auto *stop = instruction.get<program::Stop>()) {
        StringRef reason = stop->reason;
        if (reason != "reject" && reason != "abort" && reason != "exhausted" &&
            reason != "incomplete" && reason != "refused")
          return fail("interactive-stop-reason");
      } else if (const auto *op = instruction.get<program::Operation>()) {
        if (!local)
          return fail("interactive-operation");
        StringRef key = op->callee;
        std::vector<Port> inputs, expected, outputs;
        auto binding = bindings.find(key.str());
        if (binding == bindings.end())
          return fail("binding-reference");
        if (inMatch &&
            isHistoryTransition(binding->second.application.contract))
          return fail("local-match-challenge");
        auto selected = resolveBinding(binding->second.application, physical);
        if (!selected) {
          consumeError(selected.takeError());
          return fail("binding-contract");
        }
        if (auto e =
                checkParameters(binding->second.application, op->attributes))
          return fail(toString(std::move(e)));
        for (const auto &t : selected->inputs)
          expected.push_back({t.spelling()});
        for (const auto &t : selected->outputs)
          outputs.push_back({t.spelling()});
        if (!operands(op->inputs, env, inputs, consumed) ||
            inputs != expected || !bind(op->outputs, outputs, env))
          return fail("binding-operation-signature");
        for (size_t k = 0; k < inputs.size(); ++k)
          if (isDiagonalRepresentation(
                  StringRef(inputs[k].type).split('@').second)) {
            // Independent physical admission: every use is the values slot
            // of an installed contraction in this local block. Exact selected
            // signatures above enforce nominal/representation agreement and
            // dense coefficients; producer signatures enforce dense backing.
            const auto &contract = bindings.at(key.str()).application.contract;
            if (!physical || k != 1 ||
                (contract != "vector.dot" && contract != "curve.msm"))
              return fail("binding-operation-signature");
            diagonalUses.insert(op->inputs[k]);
          }
      } else if (const auto *call = instruction.get<program::LocalApply>()) {
        if (!local || target)
          return fail("algorithm-call-context");
        std::set<std::string> checked;
        if (inMatch && callsMatchUnsafe(call->callee, checked))
          return fail("local-match-challenge");
        auto f = functions.find(call->callee);
        if (f == functions.end())
          return fail("algorithm-call-symbol");
        std::vector<Port> inputs;
        if (!operands(call->inputs, env, inputs, consumed) ||
            inputs != f->second.inputs ||
            !bind(call->outputs, f->second.outputs, env))
          return fail("algorithm-call-signature");
        edges[owner.str()].insert(call->callee);
      } else if (const auto *returned = instruction.get<program::ReturnIf>()) {
        if (!target || local)
          return fail("interactive-return-type");
        std::vector<Port> condition, values;
        if (!operands({returned->condition}, env, condition, consumed) ||
            StringRef(condition[0].type).split('@').first != "bool" ||
            !operands(returned->values, env, values, consumed) ||
            values != def.outputs)
          return fail("interactive-return-type");
        std::vector<Port> affine;
        for (const auto &value : values)
          if (!duplicable(value.type))
            affine.push_back(value);
        if (!bind(returned->continuations, affine, env))
          return false;
      } else if (const auto *call = instruction.get<program::LocalCall>()) {
        if (local)
          return fail("interactive-instruction");
        auto f = functions.find(call->callee);
        if (f == functions.end())
          return fail("interactive-local-symbol");
        auto expected = f->second.inputs, outputs = f->second.outputs;
        std::vector<Port> inputs;
        if (!operands(call->inputs, env, inputs, consumed) ||
            inputs != expected || !bind(call->outputs, outputs, env))
          return fail("interactive-local-signature");
      } else if (const auto *send = instruction.get<program::Send>()) {
        if (!target || local)
          return fail("interactive-instruction");
        if (!name(send->schema) || !name(send->peer) || send->peer == def.role)
          return fail("interactive-peer");
        auto p = env.find(send->input);
        if (p == env.end() || !wireType(p->second.type))
          return fail("interactive-send");
        if (!schema(def.instance, send->schema, p->second.type))
          return false;
      } else if (const auto *receive = instruction.get<program::Receive>()) {
        if (!target || local)
          return fail("interactive-instruction");
        if (!name(receive->schema) || !name(receive->peer) ||
            receive->peer == def.role)
          return fail("interactive-peer");
        if (!name(receive->output) || !type(receive->type) ||
            !wireType(receive->type) ||
            !env.emplace(receive->output, Port{receive->type}).second)
          return fail("interactive-receive");
        if (!schema(def.instance, receive->schema, receive->type))
          return false;
      } else if (const auto *pack =
                     instruction.get<program::VariantConstruct>()) {
        if (!local)
          return fail("local-control-context");
        if (!type(pack->type))
          return false;
        auto descriptor =
            decodeVariant(StringRef(pack->type).split('@').first.str());
        if (!descriptor)
          return fail("variant-type");
        auto arm = llvm::find_if(descriptor->alternatives, [&](const auto &a) {
          return a.label == pack->alternative;
        });
        if (arm == descriptor->alternatives.end())
          return fail("variant-alternative");
        std::vector<Port> payload, expected;
        for (const auto &leaf : arm->payload) {
          auto parsed = parseBoundType(leaf, false);
          assert(parsed && "validated descriptor");
          if (physical) {
            auto selected = defaultRepresentation(*parsed);
            if (!selected) {
              consumeError(selected.takeError());
              return fail("binding-representation");
            }
            expected.push_back({selected->spelling()});
          } else
            expected.push_back({leaf});
        }
        if (!operands(pack->payload, env, payload, consumed) ||
            payload != expected)
          return fail("variant-payload");
        if (!bind({pack->output}, {{pack->type}}, env))
          return false;
      } else if (const auto *match = instruction.get<program::Match>()) {
        if (!local)
          return fail("local-control-context");
        std::vector<Port> input, captures;
        if (!operands({match->input}, env, input, consumed) ||
            !operands(match->captures, env, captures, consumed))
          return false;
        auto descriptor =
            decodeVariant(StringRef(input[0].type).split('@').first.str());
        if (!descriptor)
          return fail("variant-type");
        if (match->arms.size() != descriptor->alternatives.size())
          return fail("local-match-arms");
        std::optional<std::vector<Port>> outputs;
        for (size_t i = 0; i < match->arms.size(); ++i) {
          const auto &arm = match->arms[i];
          const auto &alternative = descriptor->alternatives[i];
          if (arm.alternative != alternative.label ||
              arm.payload.size() != alternative.payload.size())
            return fail("local-match-arm");
          Env inner;
          for (size_t j = 0; j < arm.payload.size(); ++j) {
            std::string leaf = alternative.payload[j];
            if (physical) {
              auto parsed = parseBoundType(leaf, false);
              assert(parsed && "validated descriptor");
              auto selected = defaultRepresentation(*parsed);
              if (!selected) {
                consumeError(selected.takeError());
                return fail("binding-representation");
              }
              leaf = selected->spelling();
            }
            if (!name(arm.payload[j]) ||
                !inner.emplace(arm.payload[j], Port{leaf}).second)
              return fail("local-match-payload");
          }
          for (auto [capture, port] : zip(match->captures, captures))
            if (!inner.emplace(capture, port).second)
              return fail("local-control-capture");
          std::vector<Port> yielded;
          if (!body(arm.body, std::move(inner), {}, def, owner, true, sites,
                    depth + 1, true, &yielded, true))
            return false;
          if (arm.body.back().get<program::Yield>()) {
            if (outputs && *outputs != yielded)
              return fail("local-match-yield");
            outputs = std::move(yielded);
          }
        }

        if (!outputs && !match->outputs.empty())
          return fail("local-terminal-outputs");
        if (!bind(match->outputs, outputs.value_or(std::vector<Port>{}), env))
          return false;
      } else if (const auto *branch = instruction.get<program::Conditional>()) {
        if (!local)
          return fail("local-control-context");
        std::vector<Port> condition, captured;
        if (!operands({branch->condition}, env, condition, consumed) ||
            StringRef(condition[0].type).split('@').first != "bool")
          return fail("local-if-condition");
        Env inner;
        if (!operands(branch->captures, env, captured, consumed))
          return false;
        for (auto [capture, port] : zip(branch->captures, captured))
          if (!inner.emplace(capture, port).second)
            return fail("local-control-capture");
        std::vector<Port> left, right;
        if (!body(branch->thenBody, inner, {}, def, owner, true, sites,
                  depth + 1, true, &left, inMatch) ||
            !body(branch->elseBody, inner, {}, def, owner, true, sites,
                  depth + 1, true, &right, inMatch))
          return false;

        bool leftYields = branch->thenBody.back().get<program::Yield>();
        bool rightYields = branch->elseBody.back().get<program::Yield>();
        if (!leftYields && !rightYields && !branch->outputs.empty())
          return fail("local-terminal-outputs");
        if (leftYields && rightYields && left != right)
          return fail("local-if-yield");
        if (!leftYields)
          left = right;
        if (!bind(branch->outputs, left, env))
          return false;
      } else if (const auto *nested = instruction.get<program::For>()) {
        if (!local)
          return fail("local-control-context");
        std::vector<Port> bounds;
        if (!operands({nested->lower, nested->upper}, env, bounds, consumed) ||
            StringRef(bounds[0].type).split('@').first != "index" ||
            !(bounds[0] == bounds[1]))
          return fail("local-for-bounds");
        Env inner;
        if (!name(nested->induction) ||
            !inner.emplace(nested->induction, bounds[0]).second)
          return fail("local-for-induction");
        std::vector<Port> carried;
        for (const auto &[binding, initial] : nested->carried) {
          std::vector<Port> values;
          if (!name(binding) || !operands({initial}, env, values, consumed) ||
              !inner.emplace(binding, values[0]).second)
            return fail("local-for-input");
          carried.push_back(values[0]);
        }
        for (const auto &capture : nested->captures) {
          auto p = env.find(capture);
          if (p == env.end() || consumed.count(capture) ||
              !duplicable(p->second.type) ||
              !inner.emplace(capture, p->second).second)
            return fail("local-control-capture");
        }
        auto yielded = carried;
        if (nested->conditional) {
          if (nested->body.empty() ||
              !nested->body.back().get<program::Yield>())
            return fail("local-control-yield");
          yielded.insert(yielded.begin(),
                         Port{physical ? "bool@native.bool/0" : "bool"});
        }
        if (!body(nested->body, std::move(inner), yielded, def, owner, true,
                  sites, depth + 1, true, nullptr, inMatch))
          return false;

        if (!bind(nested->outputs, carried, env))
          return false;
      } else if (const auto *nested = instruction.get<program::Loop>()) {
        if (local)
          return fail("interactive-instruction");
        if (nested->count.maximum > 1048576)
          return fail("interactive-loop-count");
        Env inner;
        std::vector<Port> count;
        if (!operands({nested->count.value}, env, count, consumed) ||
            StringRef(count[0].type).split('@').first != "index" ||
            !name(nested->count.induction) ||
            !inner.emplace(nested->count.induction, count[0]).second)
          return fail("interactive-loop-count");
        std::vector<Port> carried;
        for (const auto &[binding, initial] : nested->carried) {
          if (!name(binding))
            return false;
          std::vector<Port> values;
          if (!operands({initial}, env, values, consumed) ||
              !inner.emplace(binding, values[0]).second)
            return fail("interactive-loop-input");
          carried.push_back(values[0]);
        }
        for (const auto &capture : nested->captures) {
          auto p = env.find(capture);
          if (p == env.end() || !duplicable(p->second.type) ||
              !inner.emplace(p->first, p->second).second)
            return fail("interactive-loop-capture");
        }
        if (!body(nested->body, std::move(inner), carried, def, owner, false,
                  sites, depth + 1, true, nullptr, inMatch))
          return false;

        if (!bind(nested->outputs, carried, env))
          return false;
      } else
        return fail("interactive-instruction");
    }
    for (const auto &[service, contract] : def.services)
      if (env.count(service))
        return fail("service-port-interface");
    for (const auto &[value, port] : env)
      if (isDiagonalRepresentation(StringRef(port.type).split('@').second) &&
          !diagonalUses.count(value))
        return fail("binding-operation-signature");
    return problem.empty();
  }
  bool bodies(const std::map<std::string, Definition> &defs, bool local) {
    for (const auto &[symbol, d] : defs) {
      if (d.realization)
        continue;
      Env env;
      for (size_t i = 0; i < d.inputs.size(); ++i)
        env.emplace(d.arguments[i], d.inputs[i]);
      std::set<std::string> sites;
      if (!body(*d.body, std::move(env), d.outputs, d, symbol, local, sites))
        return false;
    }
    return true;
  }
  bool acyclic(const std::string &node, std::set<std::string> &active,
               std::map<std::string, unsigned> &heights) {
    // Cache subtree heights, not just visitation. A shared suffix contributes
    // its full depth even when it was checked first under another symbol.
    if (auto found = heights.find(node); found != heights.end())
      return active.size() + found->second <= 65 ||
             fail("interactive-call-depth");
    if (active.size() > 64)
      return fail("interactive-call-depth");
    if (!active.insert(node).second)
      return fail("interactive-call-cycle");
    unsigned height = 1;
    for (const auto &child : edges[node]) {
      if (!acyclic(child, active, heights))
        return false;
      height = std::max(height, 1 + heights.at(child));
    }
    active.erase(node);
    heights.emplace(node, height);
    return true;
  }

  bool
  environment(const std::vector<protocol::OperationBinding> &declarations) {
    if (declarations.size() > 4096)
      return fail("binding-declaration-limit");
    for (const auto &decl : declarations) {
      if (!symbols.insert(decl.name).second)
        return fail("binding-name");
      const auto &binding = decl;
      if (auto e = checkBindingDeclaration(binding.name, binding.application,
                                           physical))
        return fail(toString(std::move(e)));
      bindings.emplace(binding.name, std::move(binding));
    }
    return true;
  }
  bool cycles() {
    std::set<std::string> active;
    std::map<std::string, unsigned> heights;
    for (const auto &[name, d] : functions)
      if (!acyclic(name, active, heights))
        return false;
    for (const auto &[name, d] : participants)
      if (!acyclic(name, active, heights))
        return false;
    return true;
  }
  bool check(const program::LocalDefinitions &m) {
    if (!environment(m.bindings))
      return false;
    if (m.functions.size() > 4096)
      return fail("interactive-definition-limit");
    for (const auto &f : m.functions)
      if (!declare(f))
        return false;
    return bodies(functions, true) && cycles();
  }
  bool check(const program::Participants &m) {
    target = true;
    physical = m.stage == program::Participants::Stage::Physical;
    if (!environment(m.bindings))
      return false;
    if (m.functions.size() + m.participants.size() > 4096)
      return fail("interactive-definition-limit");
    for (const auto &f : m.functions)
      if (!declare(f))
        return false;
    for (const auto &p : m.participants)
      if (!declare(p))
        return false;
    if (!bodies(functions, true) || !bodies(participants, false) || !cycles())
      return false;
    if (m.entries.empty())
      return fail("interactive-entry");
    for (const auto &entry : m.entries) {
      if (!name(entry.name) || !symbols.insert(entry.name).second)
        return fail("interactive-entry-name");
      std::map<std::string, std::string> targets;
      if (!pairs(entry.participants, targets) || targets.empty())
        return fail("interactive-entry-targets");
      StringRef selectedInstance;
      for (const auto &[role, symbol] : targets) {
        auto d = participants.find(symbol);
        if (d == participants.end() || d->second.role != role)
          return fail("interactive-entry-role");
        StringRef instance = d->second.instance;
        if (!selectedInstance.empty() && selectedInstance != instance)
          return fail("interactive-entry-instance");
        selectedInstance = instance;
      }
    }
    return problem.empty();
  }

public:
  Error nativeLocals(const program::LocalDefinitions &module,
                     ArrayRef<LocalRealization> realizations) {
    if (realizations.size() > 4096 ||
        module.functions.size() + realizations.size() > 4096)
      return error("interactive-definition-limit");
    unsigned typeWork = 200000;
    bool limited = false;
    for (const auto &realization : realizations) {
      if (!name(realization.name) || !symbols.insert(realization.name).second)
        return error("local-realization-symbol");
      Definition d;
      d.realization = true;
      for (bool input : {true, false}) {
        const auto &ports = input ? realization.inputs : realization.outputs;
        if (ports.size() > 1024)
          return error("interactive-ports");
        for (const auto &port : ports) {
          auto type = parseBoundType(port, false);
          if (!type)
            return type.takeError();
          auto policy = nativeTypePolicy(*type, typeWork, limited);
          if (limited)
            return error("local-realization-limit");
          if (!policy || !policy->total || policy->affine)
            return error("local-realization-signature");
          (input ? d.inputs : d.outputs).push_back({port});
        }
      }
      functions.emplace(realization.name, std::move(d));
    }
    return run(module);
  }
  template <typename Root> Error run(const Root &root) {
    if (auto e = program::detail::checkNativeIRStructure(root))
      return e;
    if (detail::excessiveDepth(root))
      return error("interactive-json-depth");
    if (!check(root) && problem.empty())
      fail("interactive-admission");
    return problem.empty() ? Error::success() : error(problem);
  }
};
} // namespace

Error admitNativeLocalDefinitions(const program::LocalDefinitions &value,
                                  ArrayRef<LocalRealization> realizations) {
  return Admission().nativeLocals(value, realizations);
}
Error admit(const program::Participants &value) {
  return Admission().run(value);
}
} // namespace zkc::protocol
