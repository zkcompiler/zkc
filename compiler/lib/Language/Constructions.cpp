#include "Checker.h"
#include "zkc/Contracts/Services.h"
#include "llvm/ADT/ScopeExit.h"
#include <numeric>
using namespace llvm;
namespace zkc::language::detail {
namespace {
struct ConstructionSite {
  ConstructionRule::Kind kind;
  std::vector<std::string> path;
  bool labelled;
  Type payload;
  std::optional<unsigned> service;
  std::optional<Natural> bound;
};
} // namespace

bool Checker::constructions() {
  std::vector<unsigned> state(output.declarations.size());
  std::function<bool(DeclarationId, unsigned)> check;
  check = [&](DeclarationId id, unsigned depth) {
    auto &decl = output.declarations[id.index];
    if (depth > work.limits.typeDepth)
      return types.fail("source.limit", "construction inheritance depth",
                        decl.span);
    if (state[id.index] == 2)
      return true;
    if (state[id.index] == 1)
      return types.fail("source.construction", "cyclic construction base",
                        decl.span);
    state[id.index] = 1;
    const auto &syntax = *sources[id.index]->construction;
    const auto &target = output.declarations[decl.target->index];
    auto substitution = types.substitution(target, decl.staticArguments);
    ConstructionDefinition result;
    result.base = syntax.base;
    if (syntax.parent) {
      auto parent = resolve(decl, syntax.parent->name, syntax.parent->span);
      if (!parent)
        return false;
      const auto &base = output.declarations[parent->index];
      if (base.kind != Declaration::Kind::Construction || !base.target ||
          base.target->index != decl.target->index)
        return types.fail("source.construction",
                          "base must target the same protocol",
                          syntax.parent->span);
      if (!check(*parent, depth + 1))
        return false;
      auto arguments =
          this->arguments(decl, base, syntax.parent->arguments,
                          syntax.parent->span, syntax.parent->labels);
      if (!arguments)
        return false;
      auto bindings = types.substitution(base, *arguments);
      for (auto [expected, actual] :
           zip(base.staticArguments, decl.staticArguments)) {
        auto selected =
            types.substitute(expected, bindings, syntax.parent->span);
        if (!selected || *selected != actual)
          return types.diagnostic
                     ? false
                     : types.fail("source.construction",
                                  "base specialization differs from protocol",
                                  syntax.parent->span);
      }
      result = *base.construction;
      result.base = ConstructionDefinition::Base::Named;
      result.parent = *parent;
      result.arguments = std::move(*arguments);
      auto replace = [&](Type &value) {
        auto selected = types.substitute(value, bindings, decl.span);
        if (!selected)
          return false;
        value = std::move(*selected);
        return true;
      };
      for (auto *value : {&result.provider, &result.state})
        if (*value && !replace(**value))
          return false;
      if (result.initializer && result.initializer->component &&
          !replace(*result.initializer->component))
        return false;
      for (auto &argument : result.initializerArguments)
        if (!replace(argument))
          return false;
      for (auto &rule : result.rules)
        for (auto &argument : rule.arguments)
          if (!replace(argument))
            return false;
      if (!decl.proofFormat)
        decl.proofFormat = base.proofFormat;
      if (syntax.provider || syntax.service)
        return types.fail(
            "source.construction",
            "a derived construction inherits its provider and authority",
            decl.span);
    }
    if (syntax.base == ConstructionDefinition::Base::Authored ||
        (syntax.base == ConstructionDefinition::Base::Named &&
         result.root == ConstructionDefinition::Root::None)) {
      if (syntax.provider || syntax.service || !syntax.rules.empty())
        return types.fail("source.construction",
                          "authored base accepts only a proof format",
                          decl.span);
      decl.construction = std::move(result);
      state[id.index] = 2;
      return true;
    }
    if (syntax.base == ConstructionDefinition::Base::Native) {
      if (syntax.provider)
        return types.fail("source.construction",
                          "native base fixes its transcript provider",
                          decl.span);
      result.root = ConstructionDefinition::Root::Host;
      result.suite = syntax.suite;
      if (protocol::nativeChallengeField(result.suite).empty())
        return types.fail("source.construction",
                          "unknown native transcript suite", decl.span);
    }
    if (syntax.service) {
      auto found = llvm::find_if(target.services, [&](const ServicePort &port) {
        return port.name == syntax.service->name;
      });
      if (found == target.services.end())
        return types.fail("source.construction",
                          "replacement names no managed protocol port",
                          syntax.service->span);
      result.service = unsigned(found - target.services.begin());
    }
    if (syntax.provider) {
      auto provider = type(decl, *syntax.provider);
      if (!provider)
        return false;
      if (provider->kind != Type::Kind::Component)
        return types.fail("source.construction",
                          "transcript requires a component provider",
                          syntax.provider->span);
      auto stateType =
          types.associated(*provider, "State", syntax.provider->span);
      if (!stateType)
        return false;
      auto permissions = types.permissions(*stateType, decl.span, &decl);
      if (!permissions)
        return false;
      if (!permissions->copy || !permissions->drop)
        return types.fail(
            "source.construction",
            "source-created transcript state requires Copy and Drop",
            decl.span);
      const Declaration *owner =
          provider->symbolic
              ? &output.declarations[types.parameter(provider->domain)
                                         ->interface->index]
              : types.typeDeclaration(*provider);
      if (!types.charge(owner->members.size(), decl.span))
        return false;
      auto member = llvm::find_if(owner->members, [&](DeclarationId member) {
        return output.declarations[member.index].name == "initialize";
      });
      if (member == owner->members.end())
        return types.fail("source.construction",
                          "transcript provider requires initialize", decl.span);
      const auto &factory = output.declarations[member->index];
      auto bindings =
          types.boundMemberSubstitution(factory, *provider, decl.span);
      if (!bindings)
        return false;
      if (factory.kind != Declaration::Kind::Local || !factory.inputs.empty() ||
          factory.outputs.size() != 1 ||
          factory.parameters.size() != owner->parameters.size())
        return types.fail(
            "source.construction",
            "initialize must be a Local factory with no runtime arguments",
            decl.span);
      auto output =
          types.substitute(factory.outputs.front().type, *bindings, decl.span);
      if (!output || *output != *stateType)
        return types.diagnostic
                   ? false
                   : types.fail("source.construction",
                                "initialize must return provider State",
                                decl.span);
      result.provider = std::move(*provider);
      result.root = ConstructionDefinition::Root::Local;
      result.state = std::move(*stateType);
      result.initializer = CallableReference{*member, result.provider};
      for (const auto &parameter : factory.parameters)
        result.initializerArguments.push_back(bindings->at(parameter.atom));
    }
    if (!result.service || (!result.provider && result.suite.empty()))
      return types.fail("source.construction",
                        "construction requires a transcript provider and "
                        "replacement authority",
                        decl.span);
    if (!result.state && !syntax.rules.empty())
      return types.fail("source.construction",
                        "native provider methods are not yet available",
                        decl.span);

    std::vector<ConstructionSite> sites;
    std::function<bool(const Body &, const Substitution &, ArrayRef<unsigned>,
                       ArrayRef<std::string>, bool, unsigned)>
        collect;
    collect = [&](const Body &body, const Substitution &bindings,
                  ArrayRef<unsigned> services, ArrayRef<std::string> prefix,
                  bool labelled, unsigned depth) {
      if (depth > work.limits.callDepth)
        return types.fail("source.limit", "construction occurrence depth",
                          decl.span);
      for (const auto &operation : body.operations) {
        if (!types.charge(1, operation.span))
          return false;
        std::vector<std::string> path(prefix.begin(), prefix.end());
        if (operation.site)
          path.push_back(*operation.site);
        auto validPath = labelled && operation.site.has_value();
        if (auto repeat = std::get_if<ProtocolRepeat>(&operation.action)) {
          std::vector<unsigned> captured;
          for (auto service : repeat->services)
            captured.push_back(services[service.index]);
          if (!collect(*repeat->region, bindings, captured, prefix, labelled,
                       depth + 1))
            return false;
        } else if (auto call =
                       std::get_if<ProtocolApplication>(&operation.action)) {
          const auto &callee = output.declarations[call->callee.index];
          std::vector<Type> actual;
          for (const auto &argument : call->arguments) {
            auto value = types.substitute(argument, bindings, operation.span);
            if (!value)
              return false;
            actual.push_back(std::move(*value));
          }
          std::vector<unsigned> captured;
          for (auto service : call->services)
            captured.push_back(services[service.index]);
          if (!collect(*callee.body, types.substitution(callee, actual),
                       captured, path, validPath, depth + 1))
            return false;
        } else if (auto message = std::get_if<Exchange>(&operation.action)) {
          auto payload =
              types.substitute(body.values[message->payload.index].type,
                               bindings, operation.span);
          if (!payload)
            return false;
          sites.push_back({ConstructionRule::Kind::Message,
                           std::move(path),
                           validPath,
                           std::move(*payload),
                           {},
                           {}});
        } else if (auto query = std::get_if<ServiceQuery>(&operation.action)) {
          if (services[query->service.index] != *result.service)
            continue;
          auto payload = types.substitute(
              body.values[operation.results.front().index].type, bindings,
              operation.span);
          if (!payload)
            return false;
          sites.push_back({ConstructionRule::Kind::Query, std::move(path),
                           validPath, std::move(*payload),
                           services[query->service.index], query->bound});
        }
      }
      return true;
    };
    std::vector<unsigned> services(target.services.size());
    std::iota(services.begin(), services.end(), 0);
    if (!collect(*target.body, substitution, services, {}, true, 1))
      return false;
    std::set<std::pair<ConstructionRule::Kind, std::vector<std::string>>>
        written;
    for (const auto &source : syntax.rules) {
      ConstructionRule rule{source.kind, {}, decl.members[source.member],
                            {},          {}, source.span};
      for (const auto &part : source.path)
        rule.path.push_back(part.name);
      if (!written.emplace(rule.kind, rule.path).second)
        return types.fail("source.construction",
                          "duplicate construction selector", source.span);
      std::vector<Type> inputs{*result.state}, outputs{*result.state};
      if (rule.kind == ConstructionRule::Kind::Start) {
        for (const auto &parameter :
             ArrayRef<SyntaxName>(source.parameters).drop_front()) {
          auto found = llvm::find_if(target.inputs, [&](const Port &port) {
            return port.name == parameter.name;
          });
          if (found == target.inputs.end())
            return types.fail("source.construction",
                              "start selects no protocol input",
                              parameter.span);
          if (found->roles.size() != target.roles.size())
            return types.fail(
                "source.construction",
                "start input must be available to both participants",
                parameter.span);
          auto value =
              types.substitute(found->type, substitution, parameter.span);
          if (!value)
            return false;
          inputs.push_back(std::move(*value));
          rule.inputs.push_back(unsigned(found - target.inputs.begin()));
        }
      } else {
        if (!types.charge(sites.size(), source.span))
          return false;
        auto site = llvm::find_if(sites, [&](const ConstructionSite &site) {
          return site.labelled && site.path == rule.path &&
                 site.kind == rule.kind;
        });
        if (site == sites.end())
          return types.fail(
              "source.construction",
              "selector names no occurrence of this kind and authority",
              source.span);
        if (rule.kind == ConstructionRule::Kind::Message)
          inputs.push_back(site->payload);
        else {
          if (site->bound)
            inputs.emplace_back(Type::Kind::Index);
          // Source handlers return (state, value). Native lowering adapts this
          // ordinary source signature to its selected state-slot convention.
          Type pair(Type::Kind::Tuple);
          pair.arguments = {*result.state, site->payload};
          outputs = {std::move(pair)};
        }
      }
      auto &handler = output.declarations[rule.handler.index];
      if (!signature(handler.id))
        return false;
      if (source.parameters.size() != inputs.size())
        return types.fail("source.construction",
                          "handler parameter count differs from its occurrence",
                          source.span);
      std::set<std::string> names;
      const auto &ports = sources[handler.id.index]->inputs;
      for (auto [index, parameter] : enumerate(source.parameters)) {
        if (!names.insert(parameter.name).second)
          return types.fail("source.construction",
                            "duplicate handler parameter", parameter.span);
        if (!ports[index].type.name.empty() ||
            ports[index].type.kind != SyntaxType::Kind::Name) {
          auto annotation = type(handler, ports[index].type);
          if (!annotation)
            return false;
          if (*annotation != inputs[index])
            return types.fail("source.construction",
                              "handler annotation differs from its occurrence",
                              parameter.span);
        }
        handler.inputs.push_back(
            {parameter.name, inputs[index], {}, parameter.span});
      }
      for (const auto &value : outputs)
        handler.outputs.push_back({"result", value, {}, source.span});
      if (!body(handler.id, 1))
        return false;
      for (const auto &parameter : handler.parameters)
        rule.arguments.push_back(parameterType(parameter));
      auto prior =
          llvm::find_if(result.rules, [&](const ConstructionRule &prior) {
            return prior.kind == rule.kind && prior.path == rule.path;
          });
      if (prior == result.rules.end())
        result.rules.push_back(std::move(rule));
      else
        *prior = std::move(rule);
    }
    if (result.suite.empty()) {
      if (llvm::none_of(result.rules, [](const ConstructionRule &rule) {
            return rule.kind == ConstructionRule::Kind::Start;
          }))
        return types.fail("source.construction",
                          "construction requires on start", decl.span);
      for (const auto &site : sites)
        if (!site.labelled ||
            llvm::none_of(result.rules, [&](const ConstructionRule &rule) {
              return rule.kind == site.kind && rule.path == site.path;
            }))
          return types.fail(
              "source.construction",
              "construction does not cover every message and selected query",
              decl.span);
    }
    decl.construction = std::move(result);
    state[id.index] = 2;
    return true;
  };
  for (const auto &decl : output.declarations)
    if (decl.kind == Declaration::Kind::Construction && !check(decl.id, 1))
      return false;
  return true;
}
} // namespace zkc::language::detail
