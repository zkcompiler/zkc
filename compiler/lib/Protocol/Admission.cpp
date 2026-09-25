#include "zkc/Protocol/Admission.h"
#include "EncodingLimits.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Source/Codec.h"
#include "zkc/Source/Relations.h"
#include "llvm/ADT/StringExtras.h"
#include <set>

using namespace llvm;
namespace zkc::protocol {
namespace {
struct Port {
  std::string role, type;
  bool operator==(const Port &p) const {
    return role == p.role && type == p.type;
  }
};
struct Definition {
  std::vector<std::string> roles, parameters;
  std::vector<Port> inputs, outputs;
  std::map<std::string, std::string> dependencies;
  std::map<std::string, std::map<std::string, std::string>> agreements;
  const source::Node *record = nullptr;
  const source::Body *body = nullptr;
  source::Names arguments;
  std::set<std::string> familyParameters;
  std::string instance, role;
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
  const source::Node *current = nullptr;
  const source::Node **failureLocation;
  std::map<std::string, source::OperationBinding> bindings;
  bool target = false, physical = false, executable;
  size_t instructions = 0;
  std::map<std::string, Definition> functions, protocols;
  std::map<std::string, const source::Instance *> instances;
  std::map<std::string, std::set<std::string>> edges;
  std::set<std::string> symbols;
  std::set<std::pair<std::string, std::string>> participantIdentities;
  std::map<std::string, std::map<std::string, source::ParameterBinding>>
      participantParameters;
  std::map<std::pair<std::string, std::string>, std::string> schemas;

  bool schema(StringRef scope, StringRef name, StringRef type) {
    auto [it, inserted] =
        schemas.emplace(std::make_pair(scope.str(), name.str()), type.str());
    return inserted || it->second == type || fail("interactive-schema-type");
  }

  bool fail(StringRef code) {
    if (problem.empty()) {
      problem = code.str();
      if (failureLocation)
        *failureLocation = current;
    }
    return false;
  }
  bool name(StringRef value) {
    return identifier(value, target ? 512 : 128) || fail("interactive-name");
  }
  bool natural(StringRef value, uint64_t limit, StringRef limitReason) {
    if (value.empty() ||
        !all_of(value, [](char c) { return c >= '0' && c <= '9'; }))
      return fail("expected-natural");
    if (value.size() > 1 && value.front() == '0')
      return fail("noncanonical-natural");
    return naturalString(value, limit) || fail(limitReason);
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

  bool names(const source::Names &values, source::Names &out) {
    std::set<std::string> seen;
    for (const auto &value : values) {
      if (!name(value) || !seen.insert(value).second)
        return fail("interactive-duplicate-name");
      out.push_back(value);
    }
    return true;
  }
  bool pairs(const source::Assignments &values,
             std::map<std::string, std::string> &out, bool numeric = false) {
    for (const auto &[key, value] : values)
      if (!name(key) ||
          (numeric ? !naturalString(value, 1048576) : !name(value)) ||
          !out.emplace(key, value).second)
        return fail("interactive-binding");
    return true;
  }
  bool parameterPairs(const source::ParameterBindings &values,
                      std::map<std::string, source::ParameterBinding> &out) {
    for (const auto &[key, value] : values) {
      if (!name(key) || !out.emplace(key, value).second)
        return fail("interactive-binding");
      if (const auto *constant = std::get_if<std::string>(&value)) {
        if (!natural(*constant, 1048576, "interactive-binding"))
          return false;
      } else {
        const auto &ingress = std::get<source::FamilyIngress>(value);
        StringRef bound = ingress.bound;
        uint64_t count = 0;
        if (bound.empty() || (bound.size() > 1 && bound.front() == '0') ||
            !all_of(bound, [](char c) { return c >= '0' && c <= '9'; }))
          return fail("interactive-family-binding");
        // A canonical natural past the limit is out of bound however large.
        if (bound.getAsInteger(10, count) || count > 1048576)
          return fail("interactive-family-bound");
        if (ingress.selectors.empty())
          return fail("interactive-family-roles");
        std::set<std::string> roles;
        for (const auto &s : ingress.selectors) {
          if (!name(s.role) || !name(s.function))
            return fail("interactive-family-binding");
          if (!roles.insert(s.role).second)
            return fail("interactive-family-roles");
          std::set<std::string> arguments;
          for (const auto &argument : s.arguments) {
            if (!name(argument))
              return fail("interactive-family-binding");
            if (!arguments.insert(argument).second)
              return fail("interactive-family-argument");
          }
        }
      }
    }
    return true;
  }
  bool input(StringRef nameValue, StringRef role, StringRef spelling,
             Definition &def, bool owned) {
    if (!name(nameValue) || is_contained(def.arguments, nameValue.str()))
      return fail("interactive-argument");
    if (owned && typeKind(spelling) == "variant")
      return fail("variant-boundary");
    if (!type(spelling) || (owned && !is_contained(def.roles, role.str())))
      return fail("interactive-port-role");
    def.arguments.push_back(nameValue.str());
    def.inputs.push_back({role.str(), spelling.str()});
    return true;
  }
  bool output(StringRef role, StringRef spelling, Definition &def, bool owned) {
    if (owned && typeKind(spelling) == "variant")
      return fail("variant-boundary");
    if (!type(spelling) || (owned && !is_contained(def.roles, role.str())))
      return fail("interactive-port-role");
    def.outputs.push_back({role.str(), spelling.str()});
    return true;
  }
  bool localPorts(const std::vector<source::Parameter> &arguments,
                  const source::Names &results, Definition &def) {
    if (arguments.size() > 1024 || results.size() > 1024)
      return fail("interactive-ports");
    for (const auto &arg : arguments)
      if (!input(arg.name, "", arg.type, def, false))
        return false;
    for (const auto &result : results)
      if (!output("", result, def, false))
        return false;
    return true;
  }
  bool dependencies(const std::vector<source::Dependency> &values,
                    Definition &def) {
    for (const auto &dep : values) {
      current = &dep;
      if (!name(dep.name) || !name(dep.protocol) ||
          !def.dependencies.emplace(dep.name, dep.protocol).second ||
          !pairs(dep.agreements, def.agreements[dep.name]))
        return fail("interactive-dependency-declaration");
    }
    return true;
  }
  bool dependencyInterfaces() {
    for (const auto &[symbol, def] : protocols) {
      current = def.record;
      for (const auto &[alias, callee] : def.dependencies) {
        auto child = protocols.find(callee);
        if (child == protocols.end())
          return fail("interactive-dependency-protocol");
        for (const auto &role : child->second.roles)
          if (!is_contained(def.roles, role))
            return fail("interactive-dependency-role");
        for (const auto &[childParam, parentParam] : def.agreements.at(alias))
          if (!is_contained(child->second.parameters, childParam) ||
              !is_contained(def.parameters, parentParam))
            return fail("interactive-dependency-parameter");
      }
    }
    return true;
  }
  bool symbol(StringRef value, const source::Node &node) {
    current = &node;
    return name(value) && (symbols.insert(value.str()).second ||
                           fail("interactive-duplicate-symbol"));
  }
  bool declare(const source::Function &f) {
    if (!symbol(f.name, f))
      return false;
    Definition d;
    d.record = &f;
    d.body = f.body ? &*f.body : nullptr;
    {
      if (!f.origin || !name(f.origin->definition) ||
          f.origin->arguments.size() > 128)
        return fail("binding-logical-origin");
      std::set<std::string> parameters;
      for (const auto &[key, value] : f.origin->arguments)
        if (!name(key) || !parameters.insert(key).second ||
            installedIdentitySort(value).empty())
          return fail("binding-logical-origin");
    }
    if (!localPorts(f.arguments, f.results, d))
      return false;
    functions.emplace(f.name, std::move(d));
    return true;
  }
  bool declare(const source::Protocol &p) {
    if (!symbol(p.name, p))
      return false;
    Definition d;
    d.record = &p;
    d.body = p.body ? &*p.body : nullptr;
    if (!names(p.roles, d.roles) || d.roles.empty() ||
        !names(p.parameters, d.parameters) || !dependencies(p.dependencies, d))
      return false;
    current = &p;
    if (p.arguments.size() > 1024 || p.results.size() > 1024)
      return fail("interactive-ports");
    for (const auto &arg : p.arguments)
      if (!input(arg.name, arg.role, arg.type, d, true))
        return false;
    for (const auto &result : p.results)
      if (!output(result.role, result.type, d, true))
        return false;
    protocols.emplace(p.name, std::move(d));
    return true;
  }
  bool declare(const source::Participant &p) {
    for (const auto &a : p.arguments)
      if (typeKind(a.type) == "variant")
        return fail("variant-boundary");
    for (const auto &t : p.results)
      if (typeKind(t) == "variant")
        return fail("variant-boundary");
    if (!symbol(p.name, p) || !name(p.instance) || !name(p.role))
      return false;
    Definition d;
    d.record = &p;
    d.body = &p.body;
    d.instance = p.instance;
    d.role = p.role;
    std::map<std::string, source::ParameterBinding> params;
    if (!parameterPairs(p.parameters, params))
      return false;
    if (!participantIdentities.emplace(p.instance, p.role).second)
      return fail("interactive-participant-identity");
    auto [it, inserted] = participantParameters.emplace(p.instance, params);
    if (!inserted && it->second != params)
      return fail("interactive-instance-parameters");
    for (const auto &[key, value] : params) {
      d.parameters.push_back(key);
      if (std::holds_alternative<source::FamilyIngress>(value))
        d.familyParameters.insert(key);
    }
    if (!localPorts(p.arguments, p.results, d) ||
        !familyBindings(p.parameters, d, {{p.role, p.role}}))
      return false;
    protocols.emplace(p.name, std::move(d));
    return true;
  }
  using Env = std::map<std::string, Port>;
  bool bind(const source::Names &outputs, const std::vector<Port> &ports,
            Env &env) {
    if (outputs.size() != ports.size())
      return fail("interactive-shape");
    for (size_t i = 0; i < outputs.size(); ++i)
      if (!name(outputs[i]) || !env.emplace(outputs[i], ports[i]).second)
        return fail("interactive-ssa");
    return true;
  }
  bool operands(const source::Names &values, const Env &env,
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
    source::walk(*found->second.body, [&](const source::Instruction &i) {
      if (const auto *op = i.get<source::Operation>()) {
        auto binding = bindings.find(op->callee);
        result |= binding != bindings.end() &&
                  isHistoryTransition(binding->second.application.contract);
      } else if (const auto *call = i.get<source::AlgorithmCall>())
        result |= callsMatchUnsafe(call->callee, seen);
    });
    return result;
  }
  bool usesVariant(const std::string &callee, std::set<std::string> &seen) {
    if (!seen.insert(callee).second)
      return false;
    auto found = functions.find(callee);
    if (found == functions.end() || !found->second.body)
      return false;
    bool result = false;
    source::walk(*found->second.body, [&](const source::Instruction &i) {
      result |= i.get<source::VariantConstruct>() || i.get<source::Match>();
      if (const auto *call = i.get<source::AlgorithmCall>())
        result |= usesVariant(call->callee, seen);
    });
    return result;
  }
  bool body(const source::Body &instructionsBody, Env env,
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
      current = &instruction;
      if (++instructions > 32768)
        return fail("interactive-instruction-limit");
      if (instruction.isTerminator() !=
          (&instruction == &instructionsBody.back()))
        return fail("interactive-terminator");
      if (const auto *release = instruction.get<source::Release>()) {
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
      const auto *ret = instruction.get<source::Return>();
      const auto *yield = instruction.get<source::Yield>();
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
      if (!name(instruction.site) || !sites.insert(instruction.site).second)
        return fail("interactive-site");
      if (instruction.get<source::Incomplete>()) {
        if (!target || local)
          return fail("interactive-incomplete");
      } else if (const auto *stop = instruction.get<source::Stop>()) {
        if (local && !stop->role.empty())
          return fail("interactive-stop-role");
        if (!local && !target && !is_contained(def.roles, stop->role))
          return fail("interactive-stop-role");
        StringRef reason = stop->reason;
        if (reason != "reject" && reason != "abort" && reason != "exhausted" &&
            reason != "incomplete" && reason != "refused")
          return fail("interactive-stop-reason");
      } else if (const auto *op = instruction.get<source::Operation>()) {
        if (!local || !op->staticArguments.empty())
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
        if (auto e = checkParameters(
                binding->second.application.contract, op->attributes,
                (binding->second.application.contract == "field.constant" ||
                 binding->second.application.contract == "vector.constant")
                    ? selected->outputs[0].identity
                    : ""))
          return fail(toString(std::move(e)));
        for (const auto &t : selected->inputs)
          expected.push_back({"", t.spelling()});
        for (const auto &t : selected->outputs)
          outputs.push_back({"", t.spelling()});
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
      } else if (const auto *call = instruction.get<source::AlgorithmCall>()) {
        if (!local || target || !call->staticArguments.empty())
          return fail("algorithm-call-context");
        std::set<std::string> checked;
        if (inMatch && callsMatchUnsafe(call->callee, checked))
          return fail("local-match-challenge");
        auto f = functions.find(call->callee);
        if (f == functions.end() || !f->second.body)
          return fail("algorithm-call-symbol");
        std::vector<Port> inputs;
        if (!operands(call->inputs, env, inputs, consumed) ||
            inputs != f->second.inputs ||
            !bind(call->outputs, f->second.outputs, env))
          return fail("algorithm-call-signature");
        edges[owner.str()].insert(call->callee);
      } else if (const auto *call = instruction.get<source::LocalCall>()) {
        if (local)
          return fail("interactive-instruction");
        const auto &role = call->role;
        auto f = functions.find(call->callee);
        if (f == functions.end() || (!target && !is_contained(def.roles, role)))
          return fail("interactive-local-symbol");
        auto expected = f->second.inputs, outputs = f->second.outputs;
        for (auto &p : expected)
          p.role = role;
        for (auto &p : outputs)
          p.role = role;
        std::vector<Port> inputs;
        if (!operands(call->inputs, env, inputs, consumed) ||
            inputs != expected || !bind(call->outputs, outputs, env))
          return fail("interactive-local-signature");
      } else if (const auto *message = instruction.get<source::Message>()) {
        if (local || target)
          return fail("interactive-instruction");
        if (!name(message->schema))
          return fail("interactive-message");
        auto input = env.find(message->input);
        if (input == env.end() || message->sender == message->receiver ||
            input->second.role != message->sender ||
            !is_contained(def.roles, message->sender) ||
            !is_contained(def.roles, message->receiver) ||
            (!serializable(input->second.type) &&
             !(!executable &&
               StringRef(input->second.type).starts_with("opaque:"))))
          return fail("interactive-message-availability");
        if (!schema(owner, message->schema, input->second.type))
          return false;
        if (!name(message->output) ||
            !env.emplace(message->output,
                         Port{message->receiver, input->second.type})
                 .second)
          return fail("interactive-ssa");
      } else if (const auto *send = instruction.get<source::Send>()) {
        if (!target || local)
          return fail("interactive-instruction");
        if (!name(send->schema) || !name(send->peer) || send->peer == def.role)
          return fail("interactive-peer");
        auto p = env.find(send->input);
        if (p == env.end() || !serializable(p->second.type))
          return fail("interactive-send");
        if (!schema(def.instance, send->schema, p->second.type))
          return false;
      } else if (const auto *receive = instruction.get<source::Receive>()) {
        if (!target || local)
          return fail("interactive-instruction");
        if (!name(receive->schema) || !name(receive->peer) ||
            receive->peer == def.role)
          return fail("interactive-peer");
        if (!name(receive->output) || !type(receive->type) ||
            !serializable(receive->type) ||
            !env.emplace(receive->output, Port{"", receive->type}).second)
          return fail("interactive-receive");
        if (!schema(def.instance, receive->schema, receive->type))
          return false;
      } else if (const auto *call = instruction.get<source::ProtocolCall>()) {
        if (local)
          return fail("interactive-instruction");
        std::string callee = call->callee;
        if (!target) {
          auto dep = def.dependencies.find(callee);
          if (dep == def.dependencies.end())
            return fail("interactive-dependency");
          callee = dep->second;
        }
        auto f = protocols.find(callee);
        if (f == protocols.end() || (target && f->second.role != def.role))
          return fail("interactive-call-symbol");
        if (!target && !all_of(f->second.roles, [&](const auto &role) {
              return is_contained(def.roles, role);
            }))
          return fail("interactive-call-role");
        std::vector<Port> inputs;
        if (!operands(call->inputs, env, inputs, consumed) ||
            inputs != f->second.inputs ||
            !bind(call->outputs, f->second.outputs, env))
          return fail("interactive-call-signature");
        edges[owner.str()].insert(callee);
      } else if (const auto *pack =
                     instruction.get<source::VariantConstruct>()) {
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
            expected.push_back({"", selected->spelling()});
          } else
            expected.push_back({"", leaf});
        }
        if (!operands(pack->payload, env, payload, consumed) ||
            payload != expected)
          return fail("variant-payload");
        if (!bind({pack->output}, {{"", pack->type}}, env))
          return false;
      } else if (const auto *match = instruction.get<source::Match>()) {
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
                !inner.emplace(arm.payload[j], Port{"", leaf}).second)
              return fail("local-match-payload");
          }
          for (auto [capture, port] : zip(match->captures, captures))
            if (!inner.emplace(capture, port).second)
              return fail("local-control-capture");
          std::vector<Port> yielded;
          if (!body(arm.body, std::move(inner), {}, def, owner, true, sites,
                    depth + 1, true, &yielded, true))
            return false;
          if (arm.body.back().get<source::Yield>()) {
            if (outputs && *outputs != yielded)
              return fail("local-match-yield");
            outputs = std::move(yielded);
          }
        }
        current = &instruction;
        if (!outputs && !match->outputs.empty())
          return fail("local-terminal-outputs");
        if (!bind(match->outputs, outputs.value_or(std::vector<Port>{}), env))
          return false;
      } else if (const auto *branch = instruction.get<source::Conditional>()) {
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
        current = &instruction;
        bool leftYields = branch->thenBody.back().get<source::Yield>();
        bool rightYields = branch->elseBody.back().get<source::Yield>();
        if (!leftYields && !rightYields && !branch->outputs.empty())
          return fail("local-terminal-outputs");
        if (leftYields && rightYields && left != right)
          return fail("local-if-yield");
        if (!leftYields)
          left = right;
        if (!bind(branch->outputs, left, env))
          return false;
      } else if (const auto *nested = instruction.get<source::For>()) {
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
        if (!body(nested->body, std::move(inner), carried, def, owner, true,
                  sites, depth + 1, true, nullptr, inMatch))
          return false;
        current = &instruction;
        if (!bind(nested->outputs, carried, env))
          return false;
      } else if (const auto *nested = instruction.get<source::Loop>()) {
        if (local)
          return fail("interactive-instruction");
        if (nested->count.kind == source::LoopCount::Kind::Parameter) {
          if (!is_contained(def.parameters, nested->count.value) ||
              (target && !def.familyParameters.count(nested->count.value)))
            return fail("interactive-loop-parameter");
        } else if (!natural(nested->count.value, 1048576,
                            "interactive-loop-count"))
          return false;
        Env inner;
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
        current = &instruction;
        if (!bind(nested->outputs, carried, env))
          return false;
      } else
        return fail("interactive-instruction");
    }
    for (const auto &[value, port] : env)
      if (isDiagonalRepresentation(StringRef(port.type).split('@').second) &&
          !diagonalUses.count(value))
        return fail("binding-operation-signature");
    return problem.empty();
  }
  bool bodies(const std::map<std::string, Definition> &defs, bool local) {
    for (const auto &[symbol, d] : defs) {
      current = d.record;
      if (!d.body) {
        if (target || executable)
          return fail("interactive-external-body");
        continue;
      }
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
    current = nullptr;
    if (auto definition = protocols.find(node); definition != protocols.end())
      current = definition->second.record;
    else if (auto instance = instances.find(node); instance != instances.end())
      current = instance->second;
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

  bool environment(const std::vector<source::OperationBinding> &declarations) {
    if (declarations.size() > 4096)
      return fail("binding-declaration-limit");
    for (const auto &decl : declarations) {
      current = &decl;
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
  bool familyBindings(const source::ParameterBindings &parameters,
                      const Definition &def,
                      const std::map<std::string, std::string> &roles) {
    for (const auto &[key, value] : parameters) {
      auto family = std::get_if<source::FamilyIngress>(&value);
      if (!family)
        continue;
      if (!target && family->selectors.size() != roles.size())
        return fail("interactive-family-roles");
      for (const auto &[formal, actual] : roles) {
        auto selected =
            llvm::find_if(family->selectors, [actual = actual](const auto &p) {
              return p.role == actual;
            });
        if (selected == family->selectors.end())
          return fail("interactive-family-roles");
        auto function = functions.find(selected->function);
        if (function == functions.end() || !function->second.body)
          return fail("interactive-family-selector");
        std::set<std::string> checked;
        if (usesVariant(selected->function, checked))
          return fail("variant-family-selector");
        std::vector<Port> inputs;
        for (const auto &argument : selected->arguments) {
          auto found = llvm::find(def.arguments, argument);
          if (found == def.arguments.end())
            return fail("interactive-family-argument");
          const auto &port = def.inputs[found - def.arguments.begin()];
          if ((!target && port.role != formal) || !serializable(port.type))
            return fail("interactive-family-input");
          inputs.push_back({"", port.type});
        }
        if (function->second.inputs != inputs ||
            (function->second.outputs.size() != 1 ||
             StringRef(function->second.outputs[0].type).split('@').first !=
                 "index"))
          return fail("interactive-family-signature");
      }
    }
    return true;
  }
  bool instancesAndEntries(const source::Module &m) {
    if (m.instances.size() > 4096)
      return fail("interactive-instance-limit");
    for (const auto &instance : m.instances) {
      current = &instance;
      if (!name(instance.name) || !name(instance.protocol) ||
          !symbols.insert(instance.name).second)
        return fail("interactive-instance");
      instances.emplace(instance.name, &instance);
    }
    for (const auto &[instanceName, instance] : instances) {
      current = instance;
      auto d = protocols.find(instance->protocol);
      if (d == protocols.end())
        return fail("interactive-instance-protocol");
      std::map<std::string, source::ParameterBinding> params;
      std::map<std::string, std::string> deps, roles;
      if (!parameterPairs(instance->parameters, params) ||
          !pairs(instance->dependencies, deps) ||
          !pairs(instance->roles, roles))
        return false;
      if (params.size() != d->second.parameters.size() ||
          deps.size() != d->second.dependencies.size() ||
          roles.size() != d->second.roles.size())
        return fail("interactive-instance-signature");
      for (const auto &p : d->second.parameters)
        if (!params.count(p))
          return fail("interactive-parameter-binding");
      std::set<std::string> roleValues;
      for (const auto &p : d->second.roles)
        if (!roles.count(p) || !roleValues.insert(roles[p]).second)
          return fail("interactive-role-binding");
      if (!familyBindings(instance->parameters, d->second, roles))
        return false;
      // Entry-only: neither dynamic parents nor dynamic callees are admitted.
      for (const auto &[key, value] : params)
        if (std::holds_alternative<source::FamilyIngress>(value) &&
            !deps.empty())
          return fail("interactive-family-dependency");
      for (const auto &[key, expected] : d->second.dependencies) {
        auto actual = deps.find(key);
        if (actual == deps.end())
          return fail("interactive-dependency-binding");
        auto child = instances.find(actual->second);
        if (child == instances.end() || child->second->protocol != expected)
          return fail("interactive-dependency-protocol");
        std::map<std::string, std::string> childRoles;
        std::map<std::string, source::ParameterBinding> childParams;
        if (!pairs(child->second->roles, childRoles) ||
            !parameterPairs(child->second->parameters, childParams))
          return false;
        for (const auto &[key, value] : childParams)
          if (std::holds_alternative<source::FamilyIngress>(value))
            return fail("interactive-family-dependency");
        for (const auto &[formal, actualRole] : childRoles)
          if (!roles.count(formal) || roles[formal] != actualRole)
            return fail("interactive-dependency-role");
        for (const auto &[childParam, parentParam] :
             d->second.agreements.at(key)) {
          auto actualParam = childParams.find(childParam);
          auto expectedParam = params.find(parentParam);
          if (actualParam == childParams.end() ||
              expectedParam == params.end() ||
              actualParam->second != expectedParam->second)
            return fail("interactive-dependency-parameter-agreement");
        }
        edges[instanceName].insert(child->first);
      }
    }
    if (!cycles())
      return false;
    if (m.entries.empty() && executable)
      return fail("interactive-entry");
    for (const auto &entry : m.entries) {
      current = &entry;
      if (!name(entry.name) || !symbols.insert(entry.name).second)
        return fail("interactive-entry-name");
      if (!instances.count(entry.instance))
        return fail("interactive-entry-instance");
    }
    return true;
  }
  bool cycles() {
    std::set<std::string> active;
    std::map<std::string, unsigned> heights;
    for (const auto &[name, d] : functions)
      if (!acyclic(name, active, heights))
        return false;
    for (const auto &[name, d] : protocols)
      if (!acyclic(name, active, heights))
        return false;
    for (const auto &[name, instance] : instances)
      if (!acyclic(name, active, heights))
        return false;
    return true;
  }
  bool check(const source::Module &m) {
    current = &m;
    if (!m.relations.empty() || !m.relationViews.empty()) {
      auto checked = relation::authoredSource(m);
      if (!checked)
        return fail(toString(checked.takeError()));
    }
    if (m.isLibrary())
      return fail("interactive-format");
    if (!environment(m.bindings))
      return false;
    if (m.functions.size() + m.protocols.size() > 4096)
      return fail("interactive-definition-limit");
    for (const auto &f : m.functions)
      if (!declare(f))
        return false;
    for (const auto &p : m.protocols)
      if (!declare(p))
        return false;
    return dependencyInterfaces() && bodies(functions, true) &&
           bodies(protocols, false) && instancesAndEntries(m);
  }
  bool check(const source::Participants &m) {
    current = &m;
    target = true;
    physical = m.stage == source::Participants::Stage::Physical;
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
    for (const auto &p : m.participants) {
      bool dynamic = llvm::any_of(p.parameters, [](const auto &pair) {
        return std::holds_alternative<source::FamilyIngress>(pair.second);
      });
      for (const auto &[name, binding] : p.parameters)
        if (const auto *family = std::get_if<source::FamilyIngress>(&binding)) {
          std::set<std::string> roles, selectors;
          for (const auto &q : m.participants)
            if (q.instance == p.instance)
              roles.insert(q.role);
          for (const auto &s : family->selectors)
            selectors.insert(s.role);
          if (roles != selectors)
            return fail("interactive-family-roles");
        }
      bool invalid = false;
      source::walk(p.body, [&](const source::Instruction &ins) {
        if (auto call = ins.get<source::ProtocolCall>()) {
          auto child = llvm::find_if(m.participants, [&](const auto &q) {
            return q.name == call->callee;
          });
          invalid |= dynamic ||
                     (child != m.participants.end() &&
                      llvm::any_of(child->parameters, [](const auto &pair) {
                        return std::holds_alternative<source::FamilyIngress>(
                            pair.second);
                      }));
        }
      });
      if (invalid)
        return fail("interactive-family-dependency");
    }
    if (!bodies(functions, true) || !bodies(protocols, false) || !cycles())
      return false;
    if (m.entries.empty())
      return fail("interactive-entry");
    for (const auto &entry : m.entries) {
      current = &entry;
      if (!name(entry.name) || !symbols.insert(entry.name).second)
        return fail("interactive-entry-name");
      std::map<std::string, std::string> targets;
      if (!pairs(entry.participants, targets) || targets.empty())
        return fail("interactive-entry-targets");
      StringRef selectedInstance;
      for (const auto &[role, symbol] : targets) {
        auto d = protocols.find(symbol);
        if (d == protocols.end() || d->second.role != role)
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
  explicit Admission(bool exec, const source::Node **location)
      : failureLocation(location), executable(exec) {
    if (failureLocation)
      *failureLocation = nullptr;
  }
  template <typename Root> Error run(const Root &root) {
    if (auto e = source::checkStructure(root)) {
      if (failureLocation)
        *failureLocation = &root;
      return e;
    }
    if (auto *deep = detail::excessiveDepth(root)) {
      if (failureLocation)
        *failureLocation = deep;
      return error("interactive-json-depth");
    }
    if (!check(root) && problem.empty())
      fail("interactive-admission");
    return problem.empty() ? Error::success() : error(problem);
  }
};
} // namespace

Error admit(const source::Module &value, bool executable,
            const source::Node **failureLocation) {
  return Admission(executable, failureLocation).run(value);
}
Error admit(const source::Participants &value, bool executable,
            const source::Node **failureLocation) {
  return Admission(executable, failureLocation).run(value);
}
Error admit(const source::Content &value, bool executable,
            const source::Node **failureLocation) {
  if (const auto *module = std::get_if<source::Module>(&value))
    return admit(*module, executable, failureLocation);
  if (const auto *participants = std::get_if<source::Participants>(&value))
    return admit(*participants, executable, failureLocation);
  if (failureLocation)
    *failureLocation = &std::get<source::Construction>(value);
  return error("interactive-format");
}
} // namespace zkc::protocol
