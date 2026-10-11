#include "Checker.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Language/Builtins.h"
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
  bool proofMessage = false;
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
      if (!types.chargeConstruction(*base.construction, syntax.parent->span))
        return false;
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
      for (auto &rule : result.rules) {
        for (auto &argument : rule.arguments)
          if (!replace(argument))
            return false;
        for (auto *value : {&rule.payload, &rule.chunks})
          if (*value && !replace(**value))
            return false;
      }
      if (result.codec) {
        if (sources[id.index]->proofFormat)
          return types.fail("source.construction",
                            "an inherited record format cannot be replaced",
                            decl.span);
        auto &codec = *result.codec;
        if (!replace(codec.provider) || !replace(codec.record))
          return false;
        for (auto *method : {&codec.initialize, &codec.write, &codec.finish}) {
          if (method->target.component && !replace(*method->target.component))
            return false;
          for (auto &argument : method->arguments)
            if (!replace(argument))
              return false;
        }
      }
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
      if (syntax.provider || syntax.service || syntax.codec ||
          !syntax.rules.empty())
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
      result.nativeBase = true;
      if (protocol::nativeChallengeField(result.suite).empty())
        return types.fail("source.construction",
                          "unknown native transcript suite", decl.span);
      result.provider = domainType("Transcript", result.suite);
      auto nativeState = builtinType("transcript", {*result.provider});
      if (!nativeState)
        return types.accept(nativeState.takeError(), decl.span);
      result.state = std::move(*nativeState);
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
      if (domainSort(*provider) == "Transcript" && provider->symbolic)
        return types.fail(
            "source.construction",
            "managed transcript provider must select a closed suite",
            syntax.provider->span);
      if (domainSort(*provider) == "Transcript" && !provider->symbolic) {
        result.provider = *provider;
        result.suite = provider->domain;
        if (protocol::nativeChallengeField(result.suite).empty())
          return types.fail("source.construction",
                            "unknown managed transcript suite", decl.span);
        auto nativeState = builtinType("transcript", {*provider});
        if (!nativeState)
          return types.accept(nativeState.takeError(), decl.span);
        result.state = std::move(*nativeState);
        result.root = ConstructionDefinition::Root::Host;
      } else {
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
                            "transcript provider requires initialize",
                            decl.span);
        const auto &factory = output.declarations[member->index];
        auto bindings =
            types.boundMemberSubstitution(factory, *provider, decl.span);
        if (!bindings)
          return false;
        if (factory.kind != Declaration::Kind::Local ||
            !factory.inputs.empty() || factory.outputs.size() != 1 ||
            factory.parameters.size() != owner->parameters.size())
          return types.fail(
              "source.construction",
              "initialize must be a Local factory with no runtime arguments",
              decl.span);
        auto output = types.substitute(factory.outputs.front().type, *bindings,
                                       decl.span);
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
    }
    if (!result.service || (!result.provider && result.suite.empty()))
      return types.fail("source.construction",
                        "construction requires a transcript provider and "
                        "replacement authority",
                        decl.span);
    if (!constructionCodec(decl, syntax, result, substitution))
      return false;
    if (result.codec && target.roles.size() != 2)
      return types.fail("source.construction",
                        "record codecs require two participants", decl.span);

    std::vector<ConstructionSite> sites;
    std::function<bool(const Body &, const Substitution &, ArrayRef<unsigned>,
                       ArrayRef<unsigned>, ArrayRef<std::string>, bool,
                       unsigned)>
        collect;
    collect = [&](const Body &body, const Substitution &bindings,
                  ArrayRef<unsigned> services, ArrayRef<unsigned> roles,
                  ArrayRef<std::string> prefix, bool labelled, unsigned depth) {
      if (depth > work.limits.callDepth)
        return types.fail("source.limit", "construction occurrence depth",
                          decl.span);
      for (const auto &operation : body.operations) {
        if (!types.charge(1, operation.span))
          return false;
        for (const auto &part : prefix)
          if (!types.charge(part.size() + 1, operation.span))
            return false;
        std::vector<std::string> path(prefix.begin(), prefix.end());
        if (operation.site)
          path.push_back(*operation.site);
        auto validPath = labelled && operation.site.has_value();
        if (auto repeat = std::get_if<ProtocolRepeat>(&operation.action)) {
          std::vector<unsigned> captured;
          for (auto service : repeat->services)
            captured.push_back(services[service.index]);
          if (!collect(*repeat->region, bindings, captured, roles, prefix,
                       labelled, depth + 1))
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
          std::vector<unsigned> mappedRoles;
          for (auto role : call->roles)
            mappedRoles.push_back(roles[role]);
          if (!collect(*callee.body, types.substitution(callee, actual),
                       captured, mappedRoles, path, validPath, depth + 1))
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
                           {},
                           roles[message->receiver] ==
                                   target.services[*result.service].owner &&
                               roles[message->sender] !=
                                   target.services[*result.service].owner});
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
    std::vector<unsigned> roles(target.roles.size());
    std::iota(services.begin(), services.end(), 0);
    std::iota(roles.begin(), roles.end(), 0);
    if (!collect(*target.body, substitution, services, roles, {}, true, 1))
      return false;
    auto bytes = builtinType("bytes", {});
    if (!bytes)
      return types.accept(bytes.takeError(), decl.span);
    std::map<std::vector<std::string>, Type> chunks;
    for (const auto &rule : result.rules)
      if (rule.chunks)
        chunks[rule.path] = *rule.chunks;
    auto validChunks = [&](auto &&self, const Type &value,
                           unsigned depth) -> bool {
      if (!types.charge(1, decl.span) || depth > work.limits.typeDepth)
        return false;
      return value == *bytes ||
             (value.kind == Type::Kind::Tuple && !value.arguments.empty() &&
              all_of(value.arguments, [&](const Type &part) {
                return self(self, part, depth + 1);
              }));
    };
    for (const auto &source : syntax.rules) {
      if (source.kind != ConstructionRule::Kind::Decode)
        continue;
      if (!result.codec || source.parameters.size() != 1)
        return types.fail("source.construction",
                          "decode requires a record format and one byte input",
                          source.span);
      auto &handler = output.declarations[decl.members[source.member].index];
      if (!signature(handler.id))
        return false;
      const auto &annotation = sources[handler.id.index]->inputs.front().type;
      std::optional<Type> selected = *bytes;
      if (!annotation.name.empty() || annotation.kind != SyntaxType::Kind::Name)
        selected = type(handler, annotation);
      if (!selected)
        return false;
      if (!validChunks(validChunks, *selected, 1))
        return types.diagnostic ? false
                                : types.fail("source.construction",
                                             "decode input must be Bytes or a "
                                             "nonempty product of Bytes",
                                             source.span);
      std::vector<std::string> path;
      for (const auto &part : source.path)
        path.push_back(part.name);
      auto prior = chunks.find(path);
      if (prior != chunks.end() && prior->second != *selected)
        return types.fail("source.construction",
                          "an inherited wire shape cannot be replaced",
                          source.span);
      chunks[std::move(path)] = std::move(*selected);
    }
    auto ranges = [&](auto &&self, const Type &value) -> Type {
      Type result(Type::Kind::Tuple);
      if (value == *bytes)
        result.arguments = {Type(Type::Kind::Index), Type(Type::Kind::Index)};
      else
        for (const auto &part : value.arguments)
          result.arguments.push_back(self(self, part));
      return result;
    };
    std::set<std::pair<ConstructionRule::Kind, std::vector<std::string>>>
        written;
    for (const auto &source : syntax.rules) {
      ConstructionRule rule{source.kind, {}, decl.members[source.member],
                            {},          {}, source.span,
                            {},          {}};
      for (const auto &part : source.path)
        rule.path.push_back(part.name);
      if (!written.emplace(rule.kind, rule.path).second)
        return types.fail("source.construction",
                          "duplicate construction selector", source.span);
      std::vector<Type> inputs{*result.state}, outputs{*result.state};
      if (rule.kind == ConstructionRule::Kind::Start) {
        for (const auto &parameter :
             ArrayRef<SyntaxName>(source.parameters).drop_front()) {
          if (!types.charge(target.inputs.size(), parameter.span))
            return false;
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
                 site.kind == (protocol::isCodecRule(rule.kind)
                                   ? ConstructionRule::Kind::Message
                                   : rule.kind);
        });
        if (site == sites.end())
          return types.fail(
              "source.construction",
              "selector names no occurrence of this kind and authority",
              source.span);
        rule.payload = site->payload;
        if (protocol::isCodecRule(rule.kind)) {
          if (!result.codec || !site->proofMessage)
            return types.fail(
                "source.construction",
                "codec rule requires a producer message and record format",
                source.span);
          rule.chunks = chunks.count(rule.path) ? chunks.at(rule.path) : *bytes;
          auto pair = [](const Type &first, const Type &second) {
            Type value(Type::Kind::Tuple);
            value.arguments = {first, second};
            return value;
          };
          switch (rule.kind) {
          case ConstructionRule::Kind::Encode:
            inputs = {result.codec->record, site->payload};
            outputs = {pair(result.codec->record, *rule.chunks)};
            break;
          case ConstructionRule::Kind::Receive:
            inputs = {result.codec->record, *bytes};
            outputs = {
                pair(result.codec->record, ranges(ranges, *rule.chunks))};
            break;
          case ConstructionRule::Kind::Decode:
            inputs = {*rule.chunks};
            outputs = {site->payload};
            break;
          case ConstructionRule::Kind::Wire:
            inputs = {*result.state, *rule.chunks};
            break;
          default:
            llvm_unreachable("checked codec rule");
          }
        } else if (rule.kind == ConstructionRule::Kind::Message)
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
      if (!types.charge(result.rules.size(), source.span))
        return false;
      auto prior =
          llvm::find_if(result.rules, [&](const ConstructionRule &prior) {
            return prior.kind == rule.kind && prior.path == rule.path;
          });
      if (prior == result.rules.end())
        result.rules.push_back(std::move(rule));
      else
        *prior = std::move(rule);
    }
    if (result.codec) {
      for (const auto &site : sites) {
        if (!site.proofMessage)
          continue;
        for (auto kind :
             {ConstructionRule::Kind::Encode, ConstructionRule::Kind::Receive,
              ConstructionRule::Kind::Decode}) {
          if (!types.charge(result.rules.size(), decl.span))
            return false;
          if (!site.labelled ||
              none_of(result.rules, [&](const ConstructionRule &rule) {
                return rule.kind == kind && rule.path == site.path;
              }))
            return types.fail(
                "source.construction",
                "record codec does not cover every producer message",
                decl.span);
        }
      }
    }
    if (!result.nativeBase) {
      if (llvm::none_of(result.rules, [](const ConstructionRule &rule) {
            return rule.kind == ConstructionRule::Kind::Start;
          }))
        return types.fail("source.construction",
                          "construction requires on start", decl.span);
      for (const auto &site : sites) {
        if (!types.charge(result.rules.size(), decl.span))
          return false;
        if (!site.labelled ||
            llvm::none_of(result.rules, [&](const ConstructionRule &rule) {
              return rule.kind == site.kind && rule.path == site.path;
            }))
          return types.fail(
              "source.construction",
              "construction does not cover every message and selected query",
              decl.span);
      }
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
