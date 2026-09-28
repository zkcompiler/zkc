#include "Mathematical.h"
#include "../Model/Mathematical.h"
#include "../Resolution/Project.h"
#include "../Work.h"
#include "llvm/ADT/STLExtras.h"
#include <algorithm>
#include <map>
#include <set>

using namespace llvm;
namespace zkc::frontend::semantics {
namespace {
namespace raw = mathematical::raw;
using LogicalType = protocol::BoundType;
class Builder {
  model::Module &model;
  const syntax::Module &syntaxModule;
  const source::Module &resolved;
  const syntax::Protocol &protocol;
  const syntax::Protocol::MathematicalBody &body;
  const Declaration &declaration;
  WorkBudget &budget;
  raw::Subject source;
  mathematical::PlacementNames names;
  std::vector<model::MathematicalLocation> locations;
  std::vector<protocol::BindingApplication> operations, services;
  std::vector<protocol::BoundOperation> signatures;
  std::vector<protocol::EntropyService> entropy;
  std::vector<std::string> codecs;
  std::map<std::string, LogicalType> logicalTypes;
  std::map<std::string, uint32_t> operationNames, serviceNames, rootNames;
  std::map<std::string, raw::TypeUse> types;
  std::map<std::string, uint32_t> schemas;
  std::map<std::string, size_t> positions;
  std::set<std::string> explicitSites;
  std::vector<LogicalType> argumentTypes, resultTypes;
  std::map<std::string, LogicalType> values;
  size_t contextSize = 0;

  // Stored absolute positions survive prepending blocks; lookup is logarithmic.
  void prepend(const source::Names &block) {
    contextSize += block.size();
    for (size_t i = 0; i < block.size(); ++i)
      positions.emplace(block[i], contextSize - 1 - i);
  }
  bool charge(const source::Node &node, size_t amount = 1) {
    if (auto error = work::charge(budget, WorkAccount::GeneratedSource, amount))
      return failure(node, std::move(error));
    return true;
  }
  uint64_t nextSite = 0;

  bool fail(const source::Node &node, StringRef code, const Twine &message) {
    model.diagnostics.push_back({code.str(), message.str(), node.location});
    return false;
  }
  bool failure(const source::Node &node, Error error) {
    std::string code = "source-mathematical-declaration";
    visitErrors(error, [&](const ErrorInfoBase &info) {
      if (info.isA<Refusal>())
        code = static_cast<const Refusal &>(info).code;
    });
    return fail(node, code, toString(std::move(error)));
  }
  const protocol::BindingApplication *binding(const syntax::Reference &ref,
                                              const source::Node &node) {
    auto key = syntax::encode(ref);
    for (const auto &binding : resolved.bindings) {
      if (!charge(node))
        return nullptr;
      if (binding.name == key)
        return &binding.application;
    }
    fail(node, "source-mathematical-call",
         "this profile requires a resolved closed contract binding");
    return nullptr;
  }
  static bool same(const protocol::BindingApplication &a,
                   const protocol::BindingApplication &b) {
    return a.contract == b.contract && a.arguments == b.arguments &&
           a.implementation == b.implementation;
  }
  bool collect(const LogicalType &type, const source::Node &node) {
    if (!charge(node))
      return false;
    if (!type.representation.empty() || !type.arguments.empty() ||
        (type.kind != "field" && type.kind != "group" &&
         type.kind != "nonzero_field" && type.kind != "bool"))
      return fail(
          node, "source-mathematical-type",
          "this profile requires scalar, group, nonzero scalar or bool ports");
    logicalTypes.emplace(type.spelling(), type);
    auto codec = protocol::defaultCodec(type);
    if (codec.empty())
      return fail(node, "source-mathematical-wire",
                  "no installed canonical value codec");
    if (!is_contained(codecs, codec.str()))
      codecs.push_back(codec.str());
    return true;
  }
  bool collectCall(const syntax::Call &call) {
    if (call.operatorSymbol || call.staticArguments ||
        !call.attributes.empty() || call.annotation || call.role ||
        call.outputs.size() != 1 || !call.argumentNames.empty() ||
        call.destructure)
      return fail(
          call, "source-mathematical-call",
          "use a closed named binding with one result and positional operands");
    auto key = syntax::encode(call.callee);
    if (operationNames.count(key))
      return true;
    const auto *application = binding(call.callee, call);
    if (!application)
      return false;
    for (uint32_t i = 0; i < operations.size(); ++i)
      if (same(*application, operations[i])) {
        operationNames.emplace(key, i);
        return true;
      }
    auto signature = protocol::resolveBinding(*application, false);
    if (!signature)
      return failure(call, signature.takeError());
    if (signature->outputs.size() != 1)
      return fail(call, "source-mathematical-call",
                  "pure binding must have one result");
    for (const auto *ports : {&signature->inputs, &signature->outputs})
      for (const auto &type : *ports)
        if (!collect(type, call))
          return false;
    operationNames.emplace(key, operations.size());
    operations.push_back(*application);
    signatures.push_back(std::move(*signature));
    return true;
  }
  bool collectRoot(const syntax::Protocol::Root &root) {
    auto key = syntax::encode(root.service);
    if (serviceNames.count(key))
      return true;
    const auto *application = binding(root.service, root);
    if (!application)
      return false;
    for (uint32_t i = 0; i < services.size(); ++i)
      if (same(*application, services[i])) {
        serviceNames.emplace(key, i);
        return true;
      }
    auto descriptor = protocol::resolveEntropyService(*application);
    if (!descriptor)
      return failure(root, descriptor.takeError());
    if (!collect(descriptor->reply, root))
      return false;
    serviceNames.emplace(key, services.size());
    services.push_back(*application);
    entropy.push_back(std::move(*descriptor));
    return true;
  }
  bool role(StringRef name, raw::Role &out, const source::Node &node) {
    auto found = llvm::find(protocol.roles, name);
    if (found == protocol.roles.end())
      return fail(node, "source-mathematical-role", "unknown protocol role");
    out.index = found - protocol.roles.begin();
    return true;
  }
  bool availability(const source::Names &written, StringRef single,
                    std::vector<raw::Role> &out, const source::Node &node) {
    auto names = written.empty() ? source::Names{single.str()} : written;
    for (const auto &name : names) {
      raw::Role selected;
      if (!role(name, selected, node))
        return false;
      out.push_back(selected);
    }
    llvm::sort(out, [](auto a, auto b) { return a.index < b.index; });
    for (size_t i = 1; i < out.size(); ++i)
      if (out[i - 1].index == out[i].index)
        return fail(node, "source-mathematical-role",
                    "duplicate availability role");
    return true;
  }
  bool newValue(StringRef name, const LogicalType &type,
                const source::Node &node) {
    if (!values.emplace(name.str(), type).second)
      return fail(node, "source-value-duplicate",
                  "mathematical value names cannot shadow");
    return true;
  }
  bool value(const syntax::Place &place, raw::ValueRef &out) {
    if (!place.steps.empty())
      return fail(place, "source-mathematical-place",
                  "this profile requires scalar places");
    if (!charge(place))
      return false;
    auto found = positions.find(syntax::encode(place.root));
    if (found == positions.end())
      return fail(place, "source-mathematical-value",
                  "unknown or out-of-scope value");
    out.index = contextSize - 1 - found->second;
    return true;
  }
  uint64_t site(const syntax::Instruction &instruction) {
    auto index = nextSite++;
    if (instruction.explicitSite)
      names.sites.emplace(index, instruction.site);
    return index;
  }
  // Node ordinals are kept separately from written de Bruijn references, so
  // appending captures never changes a previously written operand.
  struct RegionValue {
    bool node;
    uint64_t index;
    LogicalType type;
    raw::RegionRef reference(uint64_t count) const {
      return {node ? count - 1 - index : count + index};
    }
  };
  bool pure(size_t &offset, raw::Body &target) {
    raw::Region region;
    std::map<std::string, RegionValue> local;
    source::Names outputs;
    auto operand = [&](const syntax::Place &place, RegionValue &out) {
      if (!place.steps.empty())
        return fail(place, "source-mathematical-place",
                    "graph operands must be scalar places");
      auto key = syntax::encode(place.root);
      if (auto found = local.find(key); found != local.end()) {
        out = found->second;
        return true;
      }
      raw::ValueRef capture;
      if (!value(place, capture))
        return false;
      out = {false, region.captures.size(), values.at(key)};
      region.captures.push_back(capture);
      local.emplace(key, out);
      return true;
    };
    auto step = uint32_t(target.steps.size());
    for (; offset < body.instructions.size(); ++offset) {
      const auto &instruction = body.instructions[offset];
      if (!charge(instruction))
        return false;
      std::string output;
      RegionValue result;
      if (const auto *call = std::get_if<syntax::Call>(&instruction.value)) {
        auto operation = operationNames.at(syntax::encode(call->callee));
        raw::PureOperation node{{operation}, {}, json::Object{}, {}};
        for (const auto &input : call->inputs) {
          RegionValue selected;
          if (!operand(input, selected))
            return false;
          node.arguments.push_back(selected.reference(region.nodes.size()));
        }
        result = {true, region.nodes.size(), signatures[operation].outputs[0]};
        locations.push_back(
            {step, uint32_t(region.nodes.size()), instruction.location});
        region.nodes.push_back(std::move(node));
        output = call->outputs[0];
      } else if (const auto *binding =
                     std::get_if<syntax::Binding>(&instruction.value)) {
        auto place = syntax::placeCandidate(binding->expression);
        if (binding->mutableBinding || binding->assignment ||
            binding->annotation || binding->destructure ||
            binding->outputs.size() != 1 || !place)
          return fail(
              instruction, "source-mathematical-expression",
              "use immutable scalar aliases or named closed operation calls");
        if (!operand(*place, result))
          return false;
        output = binding->outputs[0];
      } else
        break;
      if (!newValue(output, result.type, instruction))
        return false;
      local.emplace(output, result);
      outputs.push_back(output);
    }
    for (const auto &output : outputs)
      region.outputs.push_back(local.at(output).reference(region.nodes.size()));
    prepend(outputs);
    target.steps.push_back(raw::Pure{std::move(region)});
    return true;
  }
  bool graph(raw::Body &target) {
    for (size_t i = 0; i < body.instructions.size();) {
      const auto &instruction = body.instructions[i];
      if (!charge(instruction))
        return false;
      const bool terminal =
          std::holds_alternative<syntax::Return>(instruction.value) ||
          std::holds_alternative<source::Stop>(instruction.value);
      locations.push_back(
          {uint32_t(target.steps.size()), {}, instruction.location, terminal});
      if (std::holds_alternative<syntax::Call>(instruction.value) ||
          std::holds_alternative<syntax::Binding>(instruction.value)) {
        if (!pure(i, target))
          return false;
        continue;
      }
      ++i;
      if (const auto *query = std::get_if<syntax::Query>(&instruction.value)) {
        auto root = rootNames.find(query->root);
        raw::Role owner;
        if (root == rootNames.end() || query->outputs.size() != 1)
          return fail(instruction, "source-mathematical-query",
                      "query requires a declared root and one reply");
        if (!role(query->role, owner, instruction))
          return false;
        auto service =
            serviceNames.at(syntax::encode(body.roots[root->second].service));
        if (!newValue(query->outputs[0], entropy[service].reply, instruction))
          return false;
        target.steps.push_back(
            raw::Query{site(instruction), owner, {root->second}, {}});
        prepend({query->outputs[0]});
      } else if (const auto *message =
                     std::get_if<syntax::Message>(&instruction.value)) {
        raw::ValueRef input;
        raw::Role sender, receiver;
        if (!value(message->input, input) ||
            !role(message->sender, sender, instruction) ||
            !role(message->receiver, receiver, instruction))
          return false;
        const auto type = values.at(syntax::encode(message->input.root));
        auto [schema, fresh] =
            schemas.emplace(message->schema, source.module.wires.size());
        if (fresh) {
          auto codec = protocol::defaultCodec(type).str();
          auto index = llvm::find(codecs, codec) - codecs.begin();
          source.module.wires.push_back(
              {{uint64_t(index)}, 0, types.at(type.spelling())});
          names.wires.push_back(message->schema);
        }
        if (!fresh && source.module.wires[schema->second].type.type.index !=
                          types.at(type.spelling()).type.index)
          return fail(instruction, "source-mathematical-schema",
                      "message schema changes payload type");
        if (!newValue(message->output, type, instruction))
          return false;
        target.steps.push_back(raw::Message{
            site(instruction), {schema->second}, {}, sender, receiver, input});
        prepend({message->output});
      } else if (const auto *guard =
                     std::get_if<syntax::Guard>(&instruction.value)) {
        raw::Role owner;
        raw::ValueRef condition;
        if (!role(guard->role, owner, instruction) ||
            !value(guard->condition, condition))
          return false;
        target.steps.push_back(raw::Guard{site(instruction), owner, condition});
      } else if (const auto *returned =
                     std::get_if<syntax::Return>(&instruction.value)) {
        raw::Return result;
        for (const auto &place : returned->values) {
          raw::ValueRef input;
          if (!value(place, input))
            return false;
          result.values.push_back(input);
        }
        target.terminal = std::move(result);
        return i == body.instructions.size() ||
               fail(instruction, "source-mathematical-terminal",
                    "return must be final");
      } else if (const auto *stop =
                     std::get_if<source::Stop>(&instruction.value)) {
        raw::Role owner;
        if (stop->role.empty())
          return fail(instruction, "source-mathematical-role",
                      "stop requires an owner in this profile");
        if (!role(stop->role, owner, instruction))
          return false;
        static const std::map<std::string, raw::StopReason> reasons{
            {"reject", raw::StopReason::Reject},
            {"abort", raw::StopReason::Abort},
            {"exhausted", raw::StopReason::Exhausted},
            {"incomplete", raw::StopReason::Incomplete},
            {"refused", raw::StopReason::Refused}};
        auto reason = reasons.find(stop->reason);
        if (reason == reasons.end())
          return fail(instruction, "source-mathematical-terminal",
                      "unknown stop reason");
        target.terminal = raw::Stop{site(instruction), owner, reason->second};
        return i == body.instructions.size() ||
               fail(instruction, "source-mathematical-terminal",
                    "stop must be final");
      } else
        return fail(instruction, "source-mathematical-profile",
                    "instruction is outside the closed scalar/group profile");
    }
    return fail(protocol, "source-mathematical-terminal",
                "mathematical body requires return or stop");
  }

public:
  Builder(model::Module &model, const syntax::Module &syntaxModule,
          const source::Module &resolved, const syntax::Protocol &protocol,
          WorkBudget &budget)
      : model(model), syntaxModule(syntaxModule), resolved(resolved),
        protocol(protocol),
        body(std::get<syntax::Protocol::MathematicalBody>(protocol.body)),
        declaration(
            model.declarations.at(model.lookup({0}, protocol.name).index)),
        budget(budget) {}
  bool run() {
    if (syntaxModule.protocols.size() != 1 || resolved.instances.size() != 1 ||
        resolved.entries.size() != 1 || protocol.generic ||
        !protocol.parameters.empty() || !protocol.requirements.empty() ||
        !protocol.dependencies.empty() || !resolved.relations.empty() ||
        !resolved.relationViews.empty() || !syntaxModule.functions.empty() ||
        !syntaxModule.configurations.empty() || !syntaxModule.structs.empty() ||
        !syntaxModule.enums.empty() ||
        !syntaxModule.libraryComponents.empty() ||
        !syntaxModule.libraryInterfaces.empty() ||
        !syntaxModule.bundles.empty())
      return fail(
          protocol, "source-mathematical-profile",
          "this profile requires one closed protocol, instance and entry");
    const auto &instance = resolved.instances[0];
    if (instance.protocol != protocol.name ||
        resolved.entries[0].instance != instance.name ||
        !instance.parameters.empty() || !instance.dependencies.empty() ||
        instance.roles.size() != protocol.roles.size())
      return fail(protocol, "source-mathematical-entry",
                  "entry must close exactly this protocol");
    std::set<std::string> formalRoles, actualRoles;
    for (const auto &[formal, actual] : instance.roles) {
      if (!formalRoles.insert(formal).second ||
          !actualRoles.insert(actual).second)
        return fail(protocol, "source-mathematical-role",
                    "instance roles must be a bijection");
      source.module.roles.push_back(actual);
    }
    std::set<std::string> declaredRoles;
    for (const auto &formal : protocol.roles) {
      if (!declaredRoles.insert(formal).second)
        return fail(protocol, "source-mathematical-role",
                    "duplicate role declaration");
      auto found = llvm::find_if(instance.roles, [&](const auto &entry) {
        return entry.first == formal;
      });
      if (found == instance.roles.end())
        return fail(protocol, "source-mathematical-role",
                    "missing instance role assignment");
      source.module.entry.roles.push_back(
          {uint64_t(found - instance.roles.begin())});
    }
    for (const auto *ports : {&declaration.inputs, &declaration.outputs}) {
      auto &parsed = ports == &declaration.inputs ? argumentTypes : resultTypes;
      for (const auto &port : *ports) {
        auto type = protocol::parseBoundType(model.spelling(port.type), false);
        if (!type)
          return failure(protocol, type.takeError());
        if (!collect(*type, protocol))
          return false;
        parsed.push_back(std::move(*type));
      }
    }
    for (const auto &root : body.roots)
      if (!collectRoot(root))
        return false;
    for (const auto &instruction : body.instructions) {
      if (!charge(instruction))
        return false;
      if (instruction.explicitSite &&
          !explicitSites.insert(instruction.site).second)
        return fail(instruction, "interactive-site", "duplicate explicit site");
      if (const auto *call = std::get_if<syntax::Call>(&instruction.value))
        if (!collectCall(*call))
          return false;
    }
    auto installed =
        mathematical::Installation::create(operations, codecs, services);
    if (!installed)
      return failure(protocol, installed.takeError());
    source.manifest = installed->manifest();
    for (const auto &[spelling, type] : logicalTypes) {
      raw::TypeTemplate typeTemplate;
      if (type.kind == "bool")
        typeTemplate.body = raw::FinType{mathematical::Static::literal(2)};
      else {
        auto domain = llvm::find_if(source.manifest.domains,
                                    [identity = type.identity](const auto &id) {
                                      return id.name == identity;
                                    });
        if (domain == source.manifest.domains.end())
          return fail(protocol, "source-mathematical-domain",
                      "type domain is absent from the resolved installation");
        typeTemplate.body = raw::NominalType{
            {uint64_t(domain - source.manifest.domains.begin())},
            type.kind,
            {}};
      }
      raw::TypeUse use{{source.module.types.size()}, {}};
      types.emplace(spelling, use);
      source.module.types.push_back(std::move(typeTemplate));
    }
    for (uint32_t i = 0; i < operations.size(); ++i) {
      raw::Operation operation{{i},
                               0,
                               {},
                               {},
                               types.at(signatures[i].outputs[0].spelling()),
                               protocol::OperationPurity::Total,
                               {}};
      for (const auto &input : signatures[i].inputs)
        operation.arguments.push_back(types.at(input.spelling()));
      source.module.operations.push_back(std::move(operation));
    }
    for (uint32_t i = 0; i < services.size(); ++i)
      source.module.capabilityTypes.push_back(
          {{i}, 0, {}, types.at(entropy[i].reply.spelling())});
    raw::Definition definition;
    definition.roles = protocol.roles.size();
    for (uint32_t i = 0; i < body.roots.size(); ++i) {
      const auto &root = body.roots[i];
      if (!rootNames.emplace(root.name, i).second)
        return fail(root, "source-mathematical-root", "duplicate root name");
      std::vector<raw::Role> owners;
      if (root.owners.empty())
        return fail(root, "source-mathematical-root",
                    "root needs declared owners");
      if (!availability(root.owners, {}, owners, root))
        return false;
      raw::CapabilityUse use{{serviceNames.at(syntax::encode(root.service))},
                             {}};
      definition.capabilities.push_back({use, owners});
      for (auto &owner : owners)
        owner = source.module.entry.roles[owner.index];
      llvm::sort(owners, [](auto a, auto b) { return a.index < b.index; });
      source.module.roots.push_back({use, std::move(owners)});
      source.module.entry.capabilities.push_back({i});
      names.roots.push_back(root.name);
    }
    for (size_t i = 0; i < protocol.arguments.size(); ++i) {
      const auto &port = protocol.arguments[i];
      auto spelling = argumentTypes[i].spelling();
      raw::Port input{{}, types.at(spelling)};
      if (!availability(port.availability, port.role, input.roles, protocol) ||
          !newValue(port.name, logicalTypes.at(spelling), protocol))
        return false;
      definition.arguments.push_back(std::move(input));
      names.arguments.push_back(port.name);
    }
    prepend(names.arguments);
    for (size_t i = 0; i < protocol.results.size(); ++i) {
      const auto &port = protocol.results[i];
      raw::Port output{{}, types.at(resultTypes[i].spelling())};
      if (!availability(port.availability, port.role, output.roles, protocol))
        return false;
      definition.results.push_back(std::move(output));
    }
    if (!graph(definition.body))
      return false;
    source.module.definitions.push_back(std::move(definition));
    source.module.entry.definition = {0};
    names.protocol = protocol.name;
    names.instance = instance.name;
    names.entry = resolved.entries[0].name;
    model.mathematical = std::make_shared<model::MathematicalInput>(
        model::MathematicalInput{std::move(source), std::move(*installed),
                                 std::move(names), std::move(locations)});
    return true;
  }
};
} // namespace
bool buildMathematical(model::Module &model, const syntax::Module &syntax,
                       const source::Module &resolved, WorkBudget &budget) {
  for (const auto &protocol : syntax.protocols)
    if (std::holds_alternative<syntax::Protocol::MathematicalBody>(
            protocol.body))
      return Builder(model, syntax, resolved, protocol, budget).run();
  return true;
}
} // namespace zkc::frontend::semantics
