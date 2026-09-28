#include "Admission.h"
#include "zkc/Mathematical/Codec.h"
#include "zkc/Support/Refusal.h"
#include <algorithm>
#include <limits>

using namespace llvm;
namespace zkc::mathematical {
char AdmissionRefusal::ID = 0;

struct Subject::Storage {
  raw::Subject source;
  TypeTable types;
  std::vector<TypedDefinition> definitions;
  std::vector<ClosedInstance> instances;
  std::vector<Permission> roots;
  std::string digest;
};
const raw::Subject &Subject::source() const { return storage->source; }
const TypeTable &Subject::types() const { return storage->types; }
ArrayRef<TypedDefinition> Subject::definitions() const {
  return storage->definitions;
}
ArrayRef<ClosedInstance> Subject::instances() const {
  return storage->instances;
}
ArrayRef<Permission> Subject::roots() const { return storage->roots; }
StringRef Subject::digest() const { return storage->digest; }

bool CapabilitySignature::operator==(const CapabilitySignature &other) const {
  return service == other.service && statics == other.statics &&
         arguments == other.arguments && result == other.result;
}
Expected<std::vector<NormalStatic>>
AdmissionBuilder::parameters(uint64_t arity) {
  if (auto failure = budget.consume(arity))
    return failure;
  std::vector<NormalStatic> result;
  for (uint64_t i = 0; i < arity; ++i)
    result.push_back(NormalStatic::parameter(i));
  return result;
}
Expected<std::vector<NormalStatic>>
AdmissionBuilder::substitute(ArrayRef<Static> terms, Parameters params) {
  if (auto failure = budget.consume(terms.size()))
    return failure;
  std::vector<NormalStatic> result;
  for (const auto &term : terms) {
    auto normalized = normalize(term, params, budget);
    if (!normalized)
      return normalized.takeError();
    result.push_back(std::move(*normalized));
  }
  return result;
}
Expected<TypeId> AdmissionBuilder::type(const raw::TypeUse &use,
                                        Parameters params) {
  return types.instantiate(
      use, source.module.types.size(), params, source,
      [&](const raw::Identity &identity, const TypeShape &shape) {
        return registry.domainType(identity, shape);
      },
      budget);
}
Expected<std::vector<TypeId>>
AdmissionBuilder::typeList(ArrayRef<raw::TypeUse> uses, Parameters params) {
  if (auto failure = budget.consume(uses.size()))
    return failure;
  std::vector<TypeId> result;
  for (const auto &use : uses) {
    auto admitted = type(use, params);
    if (!admitted)
      return admitted.takeError();
    result.push_back(*admitted);
  }
  return result;
}
Expected<AdmissionBuilder::Roles> AdmissionBuilder::parties(uint64_t arity) {
  if (arity >= EncodingLimits::children)
    return error("math-role-arity");
  if (auto failure = budget.consume(arity))
    return failure;
  Roles result;
  for (uint32_t i = 0; i < arity; ++i)
    result.push_back(i);
  return result;
}
Expected<AdmissionBuilder::Roles>
AdmissionBuilder::roles(ArrayRef<raw::Role> input, uint32_t arity,
                        bool ordered) {
  if (auto failure = budget.consume(input.size()))
    return failure;
  Roles result;
  std::set<uint32_t> seen;
  for (auto role : input) {
    if (role.index >= arity ||
        !seen.insert(static_cast<uint32_t>(role.index)).second ||
        (ordered && !result.empty() && role.index <= result.back()))
      return error("math-role-binding");
    result.push_back(static_cast<uint32_t>(role.index));
  }
  return result;
}
Expected<Port> AdmissionBuilder::port(const raw::Port &input, Parameters params,
                                      uint32_t arity) {
  auto available = roles(input.roles, arity);
  if (!available)
    return available.takeError();
  auto admitted = type(input.type, params);
  if (!admitted)
    return admitted.takeError();
  return Port{std::move(*available), *admitted};
}
Expected<std::vector<Port>> AdmissionBuilder::ports(ArrayRef<raw::Port> input,
                                                    Parameters params,
                                                    uint32_t arity) {
  if (auto failure = budget.consume(input.size()))
    return failure;
  std::vector<Port> result;
  for (const auto &item : input) {
    auto admitted = port(item, params, arity);
    if (!admitted)
      return admitted.takeError();
    result.push_back(std::move(*admitted));
  }
  return result;
}
Expected<CapabilitySignature>
AdmissionBuilder::capability(const raw::CapabilityUse &use, Parameters params) {
  if (use.type.index >= source.module.capabilityTypes.size())
    return error("math-capability-type");
  const auto &declaration = source.module.capabilityTypes[use.type.index];
  if (declaration.identity.index >= source.manifest.services.size())
    return error("math-service-reference");
  if (use.statics.size() != declaration.statics)
    return error("math-static-arity");
  auto statics = substitute(use.statics, params);
  if (!statics)
    return statics.takeError();
  auto arguments = typeList(declaration.arguments, *statics);
  if (!arguments)
    return arguments.takeError();
  auto result = type(declaration.result, *statics);
  if (!result)
    return result.takeError();
  CapabilitySignature signature{
      static_cast<uint32_t>(declaration.identity.index), std::move(*statics),
      std::move(*arguments), *result};
  if (auto failure =
          registry.service(source.manifest.services[signature.service],
                           signature, types, source.manifest))
    return failure;
  return signature;
}
Expected<AdmissionBuilder::ResolvedOperation>
AdmissionBuilder::operation(uint64_t index, Parameters params) {
  if (index >= source.module.operations.size())
    return error("math-operation-reference");
  const auto &declaration = source.module.operations[index];
  if (declaration.identity.index >= source.manifest.operations.size())
    return error("math-operation-identity");
  if (params.size() != declaration.statics)
    return error("math-static-arity");
  std::vector<CapabilitySignature> capabilities;
  if (auto failure = budget.consume(declaration.capabilities.size()))
    return failure;
  for (const auto &use : declaration.capabilities) {
    auto signature = capability(use, params);
    if (!signature)
      return signature.takeError();
    capabilities.push_back(std::move(*signature));
  }
  auto arguments = typeList(declaration.arguments, params);
  if (!arguments)
    return arguments.takeError();
  auto result = type(declaration.result, params);
  if (!result)
    return result.takeError();
  OperationSignature signature{params.vec(), std::move(capabilities),
                               std::move(*arguments), *result};
  auto facts =
      registry.operation(source.manifest.operations[declaration.identity.index],
                         signature, types, source.manifest);
  if (!facts)
    return facts.takeError();
  if (facts->purity != declaration.purity ||
      facts->distinct != declaration.distinct)
    return error("math-operation-contract");
  std::optional<std::pair<uint64_t, uint64_t>> previous;
  for (auto pair : declaration.distinct) {
    if (auto failure = budget.consume())
      return failure;
    if (pair.first >= pair.second ||
        pair.second >= declaration.capabilities.size() ||
        (previous && pair <= *previous))
      return error("math-distinct-contract");
    previous = pair;
  }
  if (declaration.purity == raw::Operation::Purity::Total &&
      (!declaration.capabilities.empty() || !declaration.distinct.empty()))
    return error("math-purity");
  return ResolvedOperation{std::move(signature), std::move(*facts)};
}
Expected<TypeId> AdmissionBuilder::wire(uint64_t index, Parameters params) {
  if (index >= source.module.wires.size())
    return error("math-wire-reference");
  const auto &declaration = source.module.wires[index];
  if (declaration.identity.index >= source.manifest.wires.size())
    return error("math-wire-identity");
  if (params.size() != declaration.statics)
    return error("math-static-arity");
  auto result = type(declaration.type, params);
  if (!result)
    return result.takeError();
  if (auto failure =
          registry.wire(source.manifest.wires[declaration.identity.index],
                        params, *result, types, source.manifest))
    return failure;
  return result;
}
Expected<AdmissionBuilder::DefinitionSignature>
AdmissionBuilder::signature(uint64_t index, Parameters params) {
  if (index >= source.module.definitions.size())
    return error("math-definition-reference");
  const auto &declaration = source.module.definitions[index];
  if (params.size() != declaration.statics)
    return error("math-static-arity");
  auto roleList = parties(declaration.roles);
  if (!roleList)
    return roleList.takeError();
  auto arguments = ports(declaration.arguments, params, declaration.roles);
  if (!arguments)
    return arguments.takeError();
  auto results = ports(declaration.results, params, declaration.roles);
  if (!results)
    return results.takeError();
  std::vector<Permission> capabilities;
  for (const auto &item : declaration.capabilities) {
    auto admitted = capability(item.signature, params);
    if (!admitted)
      return admitted.takeError();
    auto permitted = roles(item.roles, declaration.roles);
    if (!permitted)
      return permitted.takeError();
    capabilities.push_back({std::move(*admitted), std::move(*permitted)});
  }
  return DefinitionSignature{static_cast<uint32_t>(declaration.roles),
                             std::move(capabilities), std::move(*arguments),
                             std::move(*results)};
}
Error AdmissionBuilder::manifest() {
  auto check = [&](Registry::Category kind,
                   ArrayRef<raw::Identity> identities) -> Error {
    std::set<std::pair<std::string, std::string>> seen;
    for (const auto &identity : identities) {
      if (auto failure = budget.consume(1 + identity.name.size() +
                                        identity.version.size()))
        return failure;
      if (identity.digest.size() != 64 ||
          !std::all_of(
              identity.digest.begin(), identity.digest.end(), [](char ch) {
                return (ch >= '0' && ch <= '9') || (ch >= 'a' && ch <= 'f');
              }))
        return error("math-package-digest");
      if (!seen.emplace(identity.name, identity.version).second)
        return error("math-duplicate-package");
      if (auto failure = registry.identity(kind, identity, source.manifest))
        return failure;
    }
    return Error::success();
  };
  if (auto failure = check(Registry::Category::Domain, source.manifest.domains))
    return failure;
  if (auto failure =
          check(Registry::Category::Operation, source.manifest.operations))
    return failure;
  if (auto failure = check(Registry::Category::Wire, source.manifest.wires))
    return failure;
  if (auto failure =
          check(Registry::Category::Service, source.manifest.services))
    return failure;
  return check(Registry::Category::Law, source.manifest.laws);
}
Error AdmissionBuilder::declarations(const json::Value &captured) {
  if (auto failure = manifest())
    return failure;
  auto moduleRoles = parties(source.module.roles.size());
  if (!moduleRoles)
    return moduleRoles.takeError();
  std::set<std::string> roleNames;
  for (const auto &role : source.module.roles) {
    if (auto failure = budget.consume(role.size()))
      return failure;
    if (!roleNames.insert(role).second)
      return error("math-duplicate-role");
  }
  std::set<std::vector<uint8_t>> typeTemplates;
  const auto &encodedTypes =
      *captured.getAsObject()->getObject("module")->getArray("types");
  for (uint32_t i = 0; i < source.module.types.size(); ++i) {
    auto bytes = encodeValue(encodedTypes[i]);
    if (!bytes)
      return bytes.takeError();
    if (auto failure = budget.consume(bytes->size()))
      return failure;
    if (!typeTemplates.insert(std::move(*bytes)).second)
      return error("math-duplicate-type");
    auto admitted = types.formTemplate(
        i, source,
        [&](const raw::Identity &identity, const TypeShape &shape) {
          return registry.domainType(identity, shape);
        },
        budget);
    if (!admitted)
      return admitted.takeError();
  }
  for (uint32_t i = 0; i < source.module.capabilityTypes.size(); ++i) {
    const auto &declaration = source.module.capabilityTypes[i];
    auto params = parameters(declaration.statics);
    if (!params)
      return params.takeError();
    raw::CapabilityUse use{{i}, {}};
    for (uint64_t p = 0; p < declaration.statics; ++p)
      use.statics.push_back(Static::parameter(p));
    auto admitted = capability(use, *params);
    if (!admitted)
      return admitted.takeError();
  }
  for (uint32_t i = 0; i < source.module.operations.size(); ++i) {
    auto params = parameters(source.module.operations[i].statics);
    if (!params)
      return params.takeError();
    auto admitted = operation(i, *params);
    if (!admitted)
      return admitted.takeError();
  }
  for (uint32_t i = 0; i < source.module.wires.size(); ++i) {
    auto params = parameters(source.module.wires[i].statics);
    if (!params)
      return params.takeError();
    auto admitted = wire(i, *params);
    if (!admitted)
      return admitted.takeError();
  }
  for (const auto &root : source.module.roots) {
    for (const auto &term : root.signature.statics)
      if (term.kind != Static::Kind::Literal)
        return error("math-root-static");
    auto admitted = capability(root.signature, {});
    if (!admitted)
      return admitted.takeError();
    auto permitted = roles(root.roles, source.module.roles.size());
    if (!permitted)
      return permitted.takeError();
    rootPermissions.push_back({std::move(*admitted), std::move(*permitted)});
  }
  for (const auto &relation : source.module.relations) {
    auto params = parameters(relation.statics);
    if (!params)
      return params.takeError();
    auto publicTypes = typeList(relation.publicInputs, *params);
    if (!publicTypes)
      return publicTypes.takeError();
    auto witnessTypes = typeList(relation.witnessInputs, *params);
    if (!witnessTypes)
      return witnessTypes.takeError();
    std::vector<Port> inputs;
    for (auto type : *publicTypes)
      inputs.push_back({{0}, type});
    for (auto type : *witnessTypes)
      inputs.push_back({{0}, type});
    Context context;
    if (auto failure = push(context, inputs))
      return failure;
    for (auto law : relation.assumptions) {
      if (auto failure = budget.consume())
        return failure;
      if (law.index >= source.manifest.laws.size())
        return error("math-law-reference");
    }
    auto formed = region(relation.body, context, {}, *params, {0}, 0);
    if (!formed)
      return formed.takeError();
    if (formed->outputs.size() != 1 ||
        !types.isCondition(formed->outputs[0].port.type))
      return error("math-relation-result");
  }
  return Error::success();
}

Expected<Subject> AdmissionBuilder::run(const json::Value &captured) {
  if (auto failure = declarations(captured))
    return failure;
  for (uint32_t i = 0; i < source.module.definitions.size(); ++i) {
    auto params = parameters(source.module.definitions[i].statics);
    if (!params)
      return params.takeError();
    auto admitted = definition(i, *params);
    if (!admitted)
      return admitted.takeError();
    definitions.push_back(std::move(*admitted));
  }
  const auto &entry = source.module.entry;
  if (entry.definition.index >= source.module.definitions.size())
    return error("math-entry-reference");
  auto roleMap = roles(entry.roles, source.module.roles.size(), false);
  if (!roleMap)
    return roleMap.takeError();
  std::vector<uint32_t> roots;
  for (auto root : entry.capabilities) {
    if (root.index >= rootPermissions.size())
      return error("math-root-reference");
    roots.push_back(static_cast<uint32_t>(root.index));
  }
  auto root =
      instance(entry.definition.index, entry.statics, *roleMap, roots, 0);
  if (!root)
    return root.takeError();
  std::vector<ClosedInstance> instances(
      std::make_move_iterator(closedInstances.begin()),
      std::make_move_iterator(closedInstances.end()));
  return Subject(std::make_shared<const Subject::Storage>(Subject::Storage{
      std::move(source), std::move(types), std::move(definitions),
      std::move(instances), std::move(rootPermissions), std::move(digest)}));
}
Expected<Subject> admit(const json::Value &value, const Registry &registry,
                        AdmissionBudget budget) {
  // Reconstruct all strings and recursive attributes into owned memory. Even a
  // programmatic LLVM value can contain borrowed strings; none escape custody.
  auto bytes = encodeValue(value);
  if (!bytes)
    return bytes.takeError();
  auto captured = decodeValue(*bytes);
  if (!captured)
    return captured.takeError();
  auto decoded = raw::decode(*captured);
  if (!decoded)
    return decoded.takeError();
  auto digest = subjectDigest(*captured);
  if (!digest)
    return digest.takeError();
  return AdmissionBuilder(std::move(*decoded), registry, budget,
                          std::move(*digest))
      .run(*captured);
}
Expected<Subject> admit(const raw::Subject &source, const Registry &registry,
                        AdmissionBudget budget) {
  auto value = raw::encode(source);
  if (!value)
    return value.takeError();
  return admit(*value, registry, budget);
}
} // namespace zkc::mathematical
