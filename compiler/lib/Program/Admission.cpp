#include "zkc/Program/Admission.h"
#include "EncodingLimits.h"
#include "Structure.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Program/Codec.h"
#include "llvm/ADT/STLExtras.h"
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
  program::Names arguments;
  std::string instance, role;
  std::map<std::string, std::string> services;
};
bool naturalString(StringRef s, uint64_t max) {
  uint64_t n = 0;
  return !s.empty() && (s.size() == 1 || s.front() != '0') &&
         all_of(s, [](char c) { return c >= '0' && c <= '9'; }) &&
         !s.getAsInteger(10, n) && n <= max;
}
class Admission {
  using RC = program::RefusalClass;
  std::string problem;
  program::RefusalClass problemClass = RC::Syntax;
  std::map<std::string, protocol::OperationBinding> bindings;
  bool target = false, physical = false;
  size_t instructions = 0;
  // Cumulative descriptor charge: each distinct physical spelling once, and
  // every binding signature position independently.
  uint64_t descriptorCharge = 0;
  std::set<std::string> chargedSpellings;
  std::map<std::string, Definition> functions, participants;
  std::map<std::string, std::set<std::string>> edges;
  std::set<std::string> symbols;
  std::set<std::pair<std::string, std::string>> participantIdentities;
  std::map<std::pair<std::string, std::string>, std::string> schemas;

  bool schema(StringRef scope, StringRef name, StringRef type) {
    auto [it, inserted] =
        schemas.emplace(std::make_pair(scope.str(), name.str()), type.str());
    return inserted || it->second == type ||
           fail(RC::Types, "interactive-schema-type");
  }

  bool fail(program::RefusalClass kind, StringRef code) {
    if (problem.empty()) {
      problem = code.str();
      problemClass = kind;
    }
    return false;
  }
  bool name(StringRef value) {
    if (value.size() > program::identifierByteLimit)
      return fail(RC::Capacity, "interactive-name-limit");
    return program::isIdentifier(value) || fail(RC::Syntax, "interactive-name");
  }
  bool natural(StringRef value, uint64_t limit, StringRef limitReason) {
    if (value.empty() ||
        !all_of(value, [](char c) { return c >= '0' && c <= '9'; }))
      return fail(RC::Syntax, "expected-natural");
    if (value.size() > 1 && value.front() == '0')
      return fail(RC::Syntax, "noncanonical-natural");
    return naturalString(value, limit) || fail(RC::Capacity, limitReason);
  }
  // Descriptor charge units of docs/spec/formats/program-bytes.md. A variant,
  // a structural application and a resource unit charge their logical
  // descriptor; an aggregate layout charges its stored child slots. Every
  // occurrence of a nested type is charged, so a cache keyed by the logical
  // spelling only avoids recomputing a value.
  std::map<std::string, uint64_t> logicalCharges;
  static uint64_t sum(uint64_t a, uint64_t b) {
    return b > UINT64_MAX - a ? UINT64_MAX : a + b;
  }
  uint64_t logicalUnits(const BoundType &type) {
    auto spelling = StringRef(type.spelling()).split('@').first.str();
    if (auto found = logicalCharges.find(spelling);
        found != logicalCharges.end())
      return found->second;
    uint64_t units = 0;
    if (type.kind == "variant") {
      auto descriptor = decodeVariant(spelling);
      if (!descriptor)
        return UINT64_MAX;
      units = 512 + 4 * uint64_t(spelling.size()) +
              256 * uint64_t(descriptor->alternatives.size());
      for (const auto &alternative : descriptor->alternatives) {
        units = sum(units, 256 * uint64_t(alternative.payload.size()));
        for (const auto &payload : alternative.payload) {
          auto parsed = parseBoundType(payload, false);
          if (!parsed) {
            consumeError(parsed.takeError());
            return UINT64_MAX;
          }
          units = sum(units, logicalUnits(*parsed));
        }
      }
    } else if (!type.arguments.empty()) {
      units = 512 + 256 * uint64_t(type.arguments.size());
      for (const auto &argument : type.arguments)
        if (argument.kind == TypeArgument::Kind::Type && argument.type)
          units = sum(units, logicalUnits(*argument.type));
    } else if (type.kind == "resource_unit") {
      units = 256;
    }
    logicalCharges.emplace(std::move(spelling), units);
    return units;
  }
  uint64_t descriptorUnits(const BoundType &type) {
    uint64_t units = logicalUnits(type);
    if (const auto &children = type.physicalChildren) {
      units = sum(units, 256 + program::descriptorChildCharge *
                                   uint64_t(children->size()));
      for (const auto &child : *children)
        units = sum(units, descriptorUnits(child));
    }
    return units;
  }
  /// Charge one parsed type against the program's descriptor budget.
  bool charge(const BoundType &type) {
    auto units = descriptorUnits(type);
    if (units > program::descriptorChargeLimit - descriptorCharge)
      return fail(RC::Capacity, "descriptor-charge-limit");
    descriptorCharge += units;
    return true;
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
  /// A port, result, received or constructed type. Each distinct spelling is
  /// charged once.
  bool type(StringRef s) {
    auto parsed = parseBoundType(s, physical);
    if (!parsed) {
      consumeError(parsed.takeError());
      return fail(RC::Types, "binding-type");
    }
    if (isDiagonalRepresentation(parsed->representation))
      return fail(RC::Types, "binding-representation");
    if (!chargedSpellings.insert(s.str()).second)
      return true;
    return charge(*parsed);
  }

  bool pairs(const protocol::Assignments &values,
             std::map<std::string, std::string> &out) {
    for (const auto &[key, value] : values) {
      if (!name(key) || !name(value))
        return false;
      if (!out.emplace(key, value).second)
        return fail(RC::NamesAndSsa, "interactive-binding");
    }
    return true;
  }
  bool input(StringRef nameValue, StringRef spelling, Definition &def) {
    if (!name(nameValue))
      return false;
    if (is_contained(def.arguments, nameValue.str()))
      return fail(RC::NamesAndSsa, "interactive-argument");
    if (!type(spelling))
      return false;
    def.arguments.push_back(nameValue.str());
    def.inputs.push_back({spelling.str()});
    return true;
  }
  bool output(StringRef spelling, Definition &def) {
    if (!type(spelling))
      return false;
    def.outputs.push_back({spelling.str()});
    return true;
  }
  bool localPorts(const std::vector<program::Parameter> &arguments,
                  const program::Names &results, Definition &def) {
    if (arguments.size() > program::listEntryLimit ||
        results.size() > program::listEntryLimit)
      return fail(RC::Capacity, "interactive-ports");
    for (const auto &arg : arguments)
      if (!input(arg.name, arg.type, def))
        return false;
    for (const auto &result : results)
      if (!output(result, def))
        return false;
    return true;
  }
  bool symbol(StringRef value) {
    return name(value) &&
           (symbols.insert(value.str()).second ||
            fail(RC::NamesAndSsa, "interactive-duplicate-symbol"));
  }
  bool declare(const program::Function &f) {
    if (!symbol(f.name))
      return false;
    Definition d;

    d.body = &f.body;
    {
      if (!f.origin)
        return fail(RC::Syntax, "binding-logical-origin");
      if (!name(f.origin->definition))
        return false;
      if (f.origin->arguments.size() > program::originAssignmentLimit)
        return fail(RC::Capacity, "binding-logical-origin");
      std::set<std::string> parameters;
      for (const auto &[key, value] : f.origin->arguments) {
        if (!name(key))
          return false;
        if (!parameters.insert(key).second)
          return fail(RC::NamesAndSsa, "binding-logical-origin");
        if (installedIdentitySort(value).empty() &&
            !staticIdentityMatches("Nat", value) &&
            !staticIdentityMatches("Type", value))
          return fail(RC::Types, "binding-logical-origin");
      }
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
        return fail(RC::Types, "variant-boundary");
    for (const auto &t : p.results)
      if (invalidBoundary(t))
        return fail(RC::Types, "variant-boundary");
    if (!symbol(p.name) || !name(p.instance) || !name(p.role))
      return false;
    Definition d;

    d.body = &p.body;
    d.instance = p.instance;
    d.role = p.role;
    if (p.services.size() + p.arguments.size() >
        program::participantInterfaceLimit)
      return fail(RC::Capacity, "interactive-port-limit");
    std::set<uint64_t> serviceIndices;
    std::set<std::string> portNames;
    for (const auto &arg : p.arguments)
      portNames.insert(arg.name);
    for (const auto &port : p.services) {
      if (!name(port.name))
        return false;
      if (randomServiceField(port.contract).empty())
        return fail(RC::UnsupportedProfile, "service-port-interface");
      if (!portNames.insert(port.name).second ||
          !serviceIndices.insert(port.inputIndex).second ||
          port.inputIndex >= p.arguments.size() + p.services.size())
        return fail(RC::NamesAndSsa, "service-port-interface");
      d.services.emplace(port.name, port.contract);
    }
    if (!participantIdentities.emplace(p.instance, p.role).second)
      return fail(RC::NamesAndSsa, "interactive-participant-identity");
    if (!localPorts(p.arguments, p.results, d))
      return false;
    participants.emplace(p.name, std::move(d));
    return true;
  }
  using Env = std::map<std::string, Port>;
  bool bind(const program::Names &outputs, const std::vector<Port> &ports,
            Env &env) {
    if (outputs.size() != ports.size())
      return fail(RC::Types, "interactive-shape");
    for (size_t i = 0; i < outputs.size(); ++i) {
      if (!name(outputs[i]))
        return false;
      if (!env.emplace(outputs[i], ports[i]).second)
        return fail(RC::NamesAndSsa, "interactive-ssa");
    }
    return true;
  }
  bool operands(const program::Names &values, const Env &env,
                std::vector<Port> &ports, std::set<std::string> &consumed) {
    for (const auto &value : values) {
      auto p = env.find(value);
      if (p == env.end())
        return fail(RC::NamesAndSsa, "interactive-unavailable");
      if (consumed.count(p->first) ||
          (!duplicable(p->second.type) && !consumed.insert(p->first).second))
        return fail(RC::AffineUse, "interactive-resource-reuse");
      ports.push_back(p->second);
    }
    return true;
  }
  bool callsMatchUnsafe(const std::string &callee,
                        std::set<std::string> &seen) {
    if (!seen.insert(callee).second)
      return false;
    auto found = functions.find(callee);
    if (found == functions.end())
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
  // Local control captures keep their names: scoped local regions canonicalize
  // aliased captures before emission. Participant control binds each distinct
  // arm formal to its parent value, so a repeated parent keeps one formal and
  // one storage binding per row. Ordinary operand consumption admits a repeated
  // parent only for duplicable values.
  bool captures(const program::Names &names, const Env &env,
                std::set<std::string> &consumed, Env &captured) {
    std::vector<Port> ports;
    if (!operands(names, env, ports, consumed))
      return false;
    for (auto [capture, port] : zip(names, ports))
      if (!captured.emplace(capture, port).second)
        return fail(RC::NamesAndSsa, "local-control-capture");
    return true;
  }
  bool captures(const protocol::Assignments &bindings, const Env &env,
                std::set<std::string> &consumed, Env &captured) {
    program::Names parents;
    for (const auto &binding : bindings)
      parents.push_back(binding.second);
    std::vector<Port> ports;
    if (!operands(parents, env, ports, consumed))
      return false;
    for (auto [binding, port] : zip(bindings, ports)) {
      if (!name(binding.first))
        return false;
      if (!captured.emplace(binding.first, port).second)
        return fail(RC::NamesAndSsa, "interactive-branch-capture");
    }
    return true;
  }
  template <typename Captures>
  static constexpr bool participantControl =
      std::is_same_v<Captures, protocol::Assignments>;

  template <typename Captures>
  bool selectedMatch(const program::SelectedMatch<Captures> &match, Env &env,
                     std::set<std::string> &consumed, const Definition &def,
                     StringRef owner, bool local, std::set<std::string> &sites,
                     unsigned depth) {
    constexpr bool participant = participantControl<Captures>;
    if (local == participant)
      return fail(RC::Syntax, "interactive-instruction");
    std::vector<Port> input;
    Env captured;
    if (!operands({match.input}, env, input, consumed) ||
        !captures(match.captures, env, consumed, captured))
      return false;
    auto descriptor =
        decodeVariant(StringRef(input[0].type).split('@').first.str());
    if (!descriptor)
      return fail(RC::Types, "variant-type");
    if (match.arms.size() != descriptor->alternatives.size())
      return fail(RC::Types, "local-match-arms");
    auto complete = parseBoundType(input[0].type, physical);
    if (!complete) {
      consumeError(complete.takeError());
      return fail(RC::Types, "variant-type");
    }
    size_t payloadOffset = 0;
    std::optional<std::vector<Port>> outputs;
    for (size_t i = 0; i < match.arms.size(); ++i) {
      const auto &arm = match.arms[i];
      const auto &alternative = descriptor->alternatives[i];
      if (arm.alternative != alternative.label ||
          arm.payload.size() != alternative.payload.size())
        return fail(RC::Types, "local-match-arm");
      Env inner;
      for (size_t j = 0; j < arm.payload.size(); ++j) {
        std::string leaf = alternative.payload[j];
        if (physical) {
          if (!complete->physicalChildren ||
              payloadOffset + j >= complete->physicalChildren->size())
            return fail(RC::Types, "binding-representation");
          leaf = (*complete->physicalChildren)[payloadOffset + j].spelling();
        }
        if (!name(arm.payload[j]))
          return false;
        if (!inner.emplace(arm.payload[j], Port{leaf}).second)
          return fail(RC::NamesAndSsa, "local-match-payload");
      }
      payloadOffset += alternative.payload.size();
      for (const auto &[capture, port] : captured)
        if (!inner.emplace(capture, port).second)
          return fail(RC::NamesAndSsa, participant
                                           ? "interactive-branch-capture"
                                           : "local-control-capture");
      std::vector<Port> yielded;
      if (!body(arm.body, std::move(inner), {}, def, owner, local, sites,
                depth + 1, true, &yielded, local))
        return false;
      if (arm.body.back().template get<program::Yield>()) {
        if (outputs && *outputs != yielded)
          return fail(RC::Types, "local-match-yield");
        outputs = std::move(yielded);
      }
    }

    if (!outputs && !match.outputs.empty())
      return fail(RC::Types, "local-terminal-outputs");
    return bind(match.outputs, outputs.value_or(std::vector<Port>{}), env);
  }

  template <typename Captures>
  bool selectedConditional(const program::SelectedConditional<Captures> &branch,
                           Env &env, std::set<std::string> &consumed,
                           const Definition &def, StringRef owner, bool local,
                           std::set<std::string> &sites, unsigned depth,
                           bool inMatch) {
    if (local == participantControl<Captures>)
      return fail(RC::Syntax, "interactive-instruction");
    std::vector<Port> condition;
    if (!operands({branch.condition}, env, condition, consumed))
      return false;
    if (StringRef(condition[0].type).split('@').first != "bool")
      return fail(RC::Types, "local-if-condition");
    Env inner;
    if (!captures(branch.captures, env, consumed, inner))
      return false;
    std::vector<Port> left, right;
    if (!body(branch.thenBody, inner, {}, def, owner, local, sites, depth + 1,
              true, &left, inMatch) ||
        !body(branch.elseBody, inner, {}, def, owner, local, sites, depth + 1,
              true, &right, inMatch))
      return false;

    bool leftYields = branch.thenBody.back().template get<program::Yield>();
    bool rightYields = branch.elseBody.back().template get<program::Yield>();
    if (!leftYields && !rightYields && !branch.outputs.empty())
      return fail(RC::Types, "local-terminal-outputs");
    if (leftYields && rightYields && left != right)
      return fail(RC::Types, "local-if-yield");
    if (!leftYields)
      left = right;
    return bind(branch.outputs, left, env);
  }

  bool body(const program::Body &instructionsBody, Env env,
            const std::vector<Port> &returns, const Definition &def,
            StringRef owner, bool local, std::set<std::string> &sites,
            unsigned depth = 0, bool loop = false,
            std::vector<Port> *inferredReturns = nullptr,
            bool inMatch = false) {
    if (depth > program::bodyNestingLimit)
      return fail(RC::Capacity, "interactive-body-depth");
    if (instructionsBody.empty())
      return fail(RC::Syntax, "interactive-body");
    std::set<std::string> consumed;
    std::set<std::string> diagonalUses;
    for (const auto &instruction : instructionsBody) {
      if (target && !local) {
        if (instruction.get<program::Stop>())
          return fail(RC::Syntax, "native-participant-terminal");
      }
      if (++instructions > program::staticInstructionLimit)
        return fail(RC::Capacity, "interactive-instruction-limit");
      if (instruction.isTerminator() !=
          (&instruction == &instructionsBody.back()))
        return fail(RC::Syntax, "interactive-terminator");
      if (const auto *release = instruction.get<program::Release>()) {
        if (!local || !instruction.site.empty())
          return fail(RC::Syntax, "interactive-release-context");
        if (!physical)
          return fail(RC::UnsupportedProfile, "interactive-release-context");
        if (release->values.size() > program::listEntryLimit)
          return fail(RC::Capacity, "interactive-port-limit");
        if (release->values.empty())
          return fail(RC::Syntax, "interactive-release-empty");
        for (const auto &value : release->values) {
          auto found = env.find(value);
          if (found == env.end())
            return fail(RC::NamesAndSsa, "interactive-release-unavailable");
          if (!consumed.insert(value).second)
            return fail(RC::AffineUse, "interactive-release-unavailable");
          if (!discardable(found->second.type))
            return fail(RC::AffineUse, "interactive-release-resource");
        }
        continue;
      }
      const auto *ret = instruction.get<program::Return>();
      const auto *yield = instruction.get<program::Yield>();
      if (ret || yield) {
        std::vector<Port> values;
        if (bool(yield) != loop)
          return fail(RC::Syntax,
                      local ? "local-terminal-context" : "interactive-return");
        if (!operands(ret ? ret->values : yield->values, env, values, consumed))
          return false;
        if (!inferredReturns && values != returns)
          return fail(RC::Types, local ? (loop ? "local-yield-types"
                                               : "function-return-types")
                                       : "interactive-return");
        if (inferredReturns)
          *inferredReturns = values;
        continue;
      }
      // Service names share the participant value namespace, while remaining
      // unavailable as data operands.
      for (const auto &[service, contract] : def.services)
        if (env.count(service))
          return fail(RC::NamesAndSsa, "service-port-interface");
      if (!name(instruction.site))
        return false;
      if (!sites.insert(instruction.site).second)
        return fail(RC::NamesAndSsa, "interactive-site");
      if (const auto *query = instruction.get<program::ServiceQuery>()) {
        if (local || !target)
          return fail(RC::Syntax, "service-query-context");
        if (!def.services.count(query->port))
          return fail(RC::NamesAndSsa, "service-query-context");
        auto method =
            serviceMethod(def.services.at(query->port), query->method);
        if (!method)
          return fail(RC::NamesAndSsa, "service-query-signature");
        if (query->inputs.size() != method->inputs.size())
          return fail(RC::Types, "service-query-signature");
        auto port = [&](BoundType logical) -> std::optional<Port> {
          if (physical) {
            auto selected = defaultRepresentation(logical);
            if (!selected) {
              consumeError(selected.takeError());
              return {};
            }
            logical = std::move(*selected);
          }
          return Port{logical.spelling()};
        };
        std::vector<Port> inputs, expected;
        for (const auto &type : method->inputs) {
          auto p = port(type);
          if (!p)
            return fail(RC::Types, "service-query-signature");
          expected.push_back(*p);
        }
        auto output = port(method->output);
        if (!output)
          return fail(RC::Types, "service-query-signature");
        if (!operands(query->inputs, env, inputs, consumed))
          return false;
        if (inputs != expected)
          return fail(RC::Types, "service-query-signature");
        if (!bind(query->outputs, {*output}, env))
          return false;
      } else if (const auto *literal =
                     instruction.get<program::BooleanConstant>()) {
        if (!local)
          return fail(RC::Syntax, "native-boolean-context");
        if (!bind({literal->output},
                  {{physical ? "bool@native.bool/0" : "bool"}}, env))
          return false;
      } else if (const auto *stop = instruction.get<program::Stop>()) {
        StringRef reason = stop->reason;
        if (reason != "reject" && reason != "abort" && reason != "exhausted" &&
            reason != "incomplete" && reason != "refused")
          return fail(RC::Syntax, "interactive-stop-reason");
      } else if (const auto *op = instruction.get<program::Operation>()) {
        if (!local)
          return fail(RC::Syntax, "interactive-operation");
        StringRef key = op->callee;
        std::vector<Port> inputs, expected, outputs;
        auto binding = bindings.find(key.str());
        if (binding == bindings.end())
          return fail(RC::NamesAndSsa, "binding-reference");
        if (inMatch &&
            isHistoryTransition(binding->second.application.contract))
          return fail(RC::UnsupportedProfile, "local-match-challenge");
        auto selected = resolveBinding(binding->second.application, physical);
        if (!selected) {
          consumeError(selected.takeError());
          return fail(RC::UnsupportedProfile, "binding-contract");
        }
        if (auto e = checkParameters(
                binding->second.application, op->attributes,
                physical ? ParameterStage::Physical : ParameterStage::Logical))
          return fail(RC::Types, toString(std::move(e)));
        for (const auto &t : selected->inputs)
          expected.push_back({t.spelling()});
        for (const auto &t : selected->outputs)
          outputs.push_back({t.spelling()});
        if (!operands(op->inputs, env, inputs, consumed))
          return false;
        if (inputs != expected)
          return fail(RC::Types, "binding-operation-signature");
        if (!bind(op->outputs, outputs, env))
          return false;
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
              return fail(RC::Types, "binding-operation-signature");
            diagonalUses.insert(op->inputs[k]);
          }
      } else if (const auto *call = instruction.get<program::LocalApply>()) {
        if (!local || target)
          return fail(RC::Syntax, "algorithm-call-context");
        std::set<std::string> checked;
        if (inMatch && callsMatchUnsafe(call->callee, checked))
          return fail(RC::UnsupportedProfile, "local-match-challenge");
        auto f = functions.find(call->callee);
        if (f == functions.end())
          return fail(RC::NamesAndSsa, "algorithm-call-symbol");
        std::vector<Port> inputs;
        if (!operands(call->inputs, env, inputs, consumed))
          return false;
        if (inputs != f->second.inputs)
          return fail(RC::Types, "algorithm-call-signature");
        if (!bind(call->outputs, f->second.outputs, env))
          return false;
        edges[owner.str()].insert(call->callee);
      } else if (const auto *returned = instruction.get<program::ReturnIf>()) {
        if (!target || local)
          return fail(RC::Syntax, "interactive-return-type");
        std::vector<Port> condition, values;
        if (!operands({returned->condition}, env, condition, consumed))
          return false;
        if (StringRef(condition[0].type).split('@').first != "bool")
          return fail(RC::Types, "interactive-return-type");
        if (!operands(returned->values, env, values, consumed))
          return false;
        if (values != def.outputs)
          return fail(RC::Types, "interactive-return-type");
        std::vector<Port> affine;
        for (const auto &value : values)
          if (!duplicable(value.type))
            affine.push_back(value);
        if (!bind(returned->continuations, affine, env))
          return false;
      } else if (const auto *call = instruction.get<program::LocalCall>()) {
        if (local)
          return fail(RC::Syntax, "interactive-instruction");
        auto f = functions.find(call->callee);
        if (f == functions.end())
          return fail(RC::NamesAndSsa, "interactive-local-symbol");
        auto expected = f->second.inputs, outputs = f->second.outputs;
        std::vector<Port> inputs;
        if (!operands(call->inputs, env, inputs, consumed))
          return false;
        if (inputs != expected)
          return fail(RC::Types, "interactive-local-signature");
        if (!bind(call->outputs, outputs, env))
          return false;
      } else if (const auto *send = instruction.get<program::Send>()) {
        if (!target || local)
          return fail(RC::Syntax, "interactive-instruction");
        if (!name(send->schema) || !name(send->peer))
          return false;
        if (send->peer == def.role)
          return fail(RC::NamesAndSsa, "interactive-peer");
        auto p = env.find(send->input);
        if (p == env.end())
          return fail(RC::NamesAndSsa, "interactive-send");
        if (!wireType(p->second.type))
          return fail(RC::Types, "interactive-send");
        if (!schema(def.instance, send->schema, p->second.type))
          return false;
      } else if (const auto *receive = instruction.get<program::Receive>()) {
        if (!target || local)
          return fail(RC::Syntax, "interactive-instruction");
        if (!name(receive->schema) || !name(receive->peer))
          return false;
        if (receive->peer == def.role)
          return fail(RC::NamesAndSsa, "interactive-peer");
        if (!name(receive->output) || !type(receive->type))
          return false;
        if (!wireType(receive->type))
          return fail(RC::Types, "interactive-receive");
        if (!env.emplace(receive->output, Port{receive->type}).second)
          return fail(RC::NamesAndSsa, "interactive-receive");
        if (!schema(def.instance, receive->schema, receive->type))
          return false;
      } else if (const auto *pack =
                     instruction.get<program::VariantConstruct>()) {
        if (!local)
          return fail(RC::Syntax, "local-control-context");
        if (!type(pack->type))
          return false;
        auto descriptor =
            decodeVariant(StringRef(pack->type).split('@').first.str());
        if (!descriptor)
          return fail(RC::Types, "variant-type");
        auto arm = llvm::find_if(descriptor->alternatives, [&](const auto &a) {
          return a.label == pack->alternative;
        });
        if (arm == descriptor->alternatives.end())
          return fail(RC::Types, "variant-alternative");
        std::vector<Port> payload, expected;
        auto complete = parseBoundType(pack->type, physical);
        if (!complete) {
          consumeError(complete.takeError());
          return fail(RC::Types, "variant-type");
        }
        size_t offset = 0;
        for (auto previous = descriptor->alternatives.begin(); previous != arm;
             ++previous)
          offset += previous->payload.size();
        for (auto [i, leaf] : enumerate(arm->payload)) {
          if (physical) {
            if (!complete->physicalChildren ||
                offset + i >= complete->physicalChildren->size())
              return fail(RC::Types, "binding-representation");
            expected.push_back(
                {(*complete->physicalChildren)[offset + i].spelling()});
          } else
            expected.push_back({leaf});
        }
        if (!operands(pack->payload, env, payload, consumed))
          return false;
        if (payload != expected)
          return fail(RC::Types, "variant-payload");
        if (!bind({pack->output}, {{pack->type}}, env))
          return false;
      } else if (const auto *match = instruction.get<program::Match>()) {
        if (!selectedMatch(*match, env, consumed, def, owner, local, sites,
                           depth))
          return false;
      } else if (const auto *match =
                     instruction.get<program::ParticipantMatch>()) {
        if (!selectedMatch(*match, env, consumed, def, owner, local, sites,
                           depth))
          return false;
      } else if (const auto *branch = instruction.get<program::Conditional>()) {
        if (!selectedConditional(*branch, env, consumed, def, owner, local,
                                 sites, depth, inMatch))
          return false;
      } else if (const auto *branch =
                     instruction.get<program::ParticipantConditional>()) {
        if (!selectedConditional(*branch, env, consumed, def, owner, local,
                                 sites, depth, inMatch))
          return false;
      } else if (const auto *nested = instruction.get<program::For>()) {
        if (!local)
          return fail(RC::Syntax, "local-control-context");
        std::vector<Port> bounds;
        if (!operands({nested->lower, nested->upper}, env, bounds, consumed))
          return false;
        if (StringRef(bounds[0].type).split('@').first != "index" ||
            !(bounds[0] == bounds[1]))
          return fail(RC::Types, "local-for-bounds");
        Env inner;
        if (!name(nested->induction))
          return false;
        if (!inner.emplace(nested->induction, bounds[0]).second)
          return fail(RC::NamesAndSsa, "local-for-induction");
        std::vector<Port> carried;
        for (const auto &[binding, initial] : nested->carried) {
          std::vector<Port> values;
          if (!name(binding) || !operands({initial}, env, values, consumed))
            return false;
          if (!inner.emplace(binding, values[0]).second)
            return fail(RC::NamesAndSsa, "local-for-input");
          carried.push_back(values[0]);
        }
        for (const auto &capture : nested->captures) {
          auto p = env.find(capture);
          if (p == env.end())
            return fail(RC::NamesAndSsa, "local-control-capture");
          if (consumed.count(capture) || !duplicable(p->second.type))
            return fail(RC::AffineUse, "local-control-capture");
          if (!inner.emplace(capture, p->second).second)
            return fail(RC::NamesAndSsa, "local-control-capture");
        }
        auto yielded = carried;
        if (nested->conditional) {
          if (nested->body.empty() ||
              !nested->body.back().get<program::Yield>())
            return fail(RC::Syntax, "local-control-yield");
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
          return fail(RC::Syntax, "interactive-instruction");
        if (nested->count.maximum > program::loopMaximumLimit)
          return fail(RC::Capacity, "interactive-loop-count");
        // The body is a nested lexical environment: its formals only. Names
        // bound in it are not visible after the loop.
        Env inner;
        std::vector<Port> count;
        if (!operands({nested->count.value}, env, count, consumed))
          return false;
        if (StringRef(count[0].type).split('@').first != "index")
          return fail(RC::Types, "interactive-loop-count");
        if (!name(nested->count.induction))
          return false;
        if (!inner.emplace(nested->count.induction, count[0]).second)
          return fail(RC::NamesAndSsa, "interactive-loop-count");
        std::vector<Port> carried;
        for (const auto &[binding, initial] : nested->carried) {
          if (!name(binding))
            return false;
          std::vector<Port> values;
          if (!operands({initial}, env, values, consumed))
            return false;
          if (!inner.emplace(binding, values[0]).second)
            return fail(RC::NamesAndSsa, "interactive-loop-input");
          carried.push_back(values[0]);
        }
        for (const auto &[local, parent] : nested->captures) {
          if (!name(local))
            return false;
          auto p = env.find(parent);
          if (p == env.end())
            return fail(RC::NamesAndSsa, "interactive-loop-capture");
          if (!duplicable(p->second.type))
            return fail(RC::AffineUse, "interactive-loop-capture");
          if (!inner.emplace(local, p->second).second)
            return fail(RC::NamesAndSsa, "interactive-loop-capture");
        }
        if (!body(nested->body, std::move(inner), carried, def, owner, false,
                  sites, depth + 1, true, nullptr, inMatch))
          return false;

        if (!bind(nested->outputs, carried, env))
          return false;
      } else
        return fail(RC::Syntax, "interactive-instruction");
    }
    for (const auto &[service, contract] : def.services)
      if (env.count(service))
        return fail(RC::NamesAndSsa, "service-port-interface");
    for (const auto &[value, port] : env)
      if (isDiagonalRepresentation(StringRef(port.type).split('@').second) &&
          !diagonalUses.count(value))
        return fail(RC::Types, "binding-operation-signature");
    return problem.empty();
  }
  bool bodies(const std::map<std::string, Definition> &defs, bool local) {
    for (const auto &[symbol, d] : defs) {
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
             fail(RC::Capacity, "interactive-call-depth");
    if (active.size() > 64)
      return fail(RC::Capacity, "interactive-call-depth");
    if (!active.insert(node).second)
      return fail(RC::UnsupportedProfile, "interactive-call-cycle");
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

  /// Every signature position of a binding is charged, including bindings no
  /// instruction uses, as are its declared physical arguments.
  bool chargeSignature(const BindingApplication &application) {
    auto selected = resolveBinding(application, physical);
    if (!selected) {
      consumeError(selected.takeError());
      return fail(RC::UnsupportedProfile, "binding-contract");
    }
    for (const auto &type : selected->inputs)
      if (!charge(type))
        return false;
    for (const auto &type : selected->outputs)
      if (!charge(type))
        return false;
    for (const auto &spelling : application.physicalArguments) {
      auto parsed = parseBoundType(spelling, true);
      if (!parsed) {
        consumeError(parsed.takeError());
        return fail(RC::Types, "binding-type");
      }
      if (!charge(*parsed))
        return false;
    }
    return true;
  }

  bool
  environment(const std::vector<protocol::OperationBinding> &declarations) {
    if (declarations.size() > program::bindingLimit)
      return fail(RC::Capacity, "binding-declaration-limit");
    for (const auto &decl : declarations) {
      if (decl.application.arguments.size() > program::bindingArgumentLimit ||
          decl.application.physicalArguments.size() >
              program::bindingArgumentLimit)
        return fail(RC::Capacity, "binding-static-arity");
      // Binding names are carrier identifiers.
      if (!name(decl.name))
        return false;
      if (!symbols.insert(decl.name).second)
        return fail(RC::NamesAndSsa, "binding-name");
      const auto &binding = decl;
      if (auto e = checkBindingDeclaration(binding.name, binding.application,
                                           physical))
        return fail(RC::UnsupportedProfile, toString(std::move(e)));
      if (!chargeSignature(binding.application))
        return false;
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
    if (m.functions.size() > program::definitionLimit)
      return fail(RC::Capacity, "interactive-definition-limit");
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
    if (m.functions.size() + m.participants.size() > program::definitionLimit)
      return fail(RC::Capacity, "interactive-definition-limit");
    if (m.entries.size() > program::entryLimit)
      return fail(RC::Capacity, "interactive-entry-limit");
    for (const auto &f : m.functions)
      if (!declare(f))
        return false;
    for (const auto &p : m.participants)
      if (!declare(p))
        return false;
    if (!bodies(functions, true) || !bodies(participants, false) || !cycles())
      return false;
    if (m.entries.empty() && (!m.participants.empty() || m.functions.empty()))
      return fail(RC::Syntax, "interactive-entry");
    if (m.participants.empty() && !m.entries.empty())
      return fail(RC::Syntax, "interactive-entry");
    for (const auto &entry : m.entries) {
      if (!name(entry.name))
        return false;
      if (!symbols.insert(entry.name).second)
        return fail(RC::NamesAndSsa, "interactive-entry-name");
      if (entry.participants.size() > program::listEntryLimit)
        return fail(RC::Capacity, "interactive-entry-targets");
      std::map<std::string, std::string> targets;
      if (!pairs(entry.participants, targets))
        return false;
      if (targets.empty())
        return fail(RC::Syntax, "interactive-entry-targets");
      StringRef selectedInstance;
      for (const auto &[role, symbol] : targets) {
        auto d = participants.find(symbol);
        if (d == participants.end() || d->second.role != role)
          return fail(RC::NamesAndSsa, "interactive-entry-role");
        StringRef instance = d->second.instance;
        if (!selectedInstance.empty() && selectedInstance != instance)
          return fail(RC::NamesAndSsa, "interactive-entry-instance");
        selectedInstance = instance;
      }
    }
    return problem.empty();
  }

  template <typename Root> Error checkRoot(const Root &root) {
    if (detail::excessiveDepth(root))
      return program::refuse(RC::Capacity, "interactive-json-depth");
    if (!check(root) && problem.empty())
      fail(RC::Syntax, "interactive-admission");
    return problem.empty() ? Error::success()
                           : program::refuse(problemClass, problem);
  }

public:
  Error executionDefinitions(const program::LocalDefinitions &module,
                             bool selected) {
    target = true;
    physical = selected;
    return run(module);
  }
  template <typename Root>
  Error run(const Root &root, AdmissionReport *report = nullptr) {
    if (auto e = program::detail::checkNativeIRStructure(root))
      return e;
    if (auto e = checkRoot(root))
      return e;
    if (report) {
      report->staticInstructions = instructions;
      report->descriptorCharge = descriptorCharge;
    }
    return Error::success();
  }
};
} // namespace

Error admitNativeLocalDefinitions(const program::LocalDefinitions &value) {
  return Admission().run(value);
}
Error admitExecutionDefinitions(const program::LocalDefinitions &value,
                                bool physical) {
  return Admission().executionDefinitions(value, physical);
}
Error admit(const program::Participants &value, AdmissionReport *report) {
  return Admission().run(value, report);
}
} // namespace zkc::protocol
