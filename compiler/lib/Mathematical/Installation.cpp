#include "zkc/Mathematical/Installation.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Mathematical/Codec.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <set>

using namespace llvm;
namespace zkc::mathematical {
namespace {
bool same(const raw::Identity &left, const raw::Identity &right) {
  return left.name == right.name && left.version == right.version &&
         left.digest == right.digest;
}

Expected<raw::Identity> pin(StringRef name, json::Array descriptor) {
  auto encoded = encodeValue(json::Value(std::move(descriptor)));
  if (!encoded)
    return encoded.takeError();
  SHA256 hash;
  hash.update("zkc.math.installation.v1");
  hash.update(StringRef("\0", 1));
  hash.update(*encoded);
  return raw::Identity{name.str(), "1", toHex(hash.final(), true)};
}

Error collectType(const protocol::BoundType &type,
                  std::set<std::string> &domains) {
  if (!type.representation.empty() || !type.arguments.empty())
    return error("math-installed-type-subset");
  if (type.kind == "bool" && type.identity.empty())
    return Error::success();
  const auto *declaration = protocol::typeDeclaration(type.kind);
  const auto *permissions = protocol::typePermissions(type.kind);
  if (!declaration || declaration->parameters.size() != 1 || !permissions ||
      !permissions->copy || !permissions->drop ||
      (permissions->custody != protocol::Custody::PublicValue &&
       permissions->custody != protocol::Custody::PrivateImmutable))
    return error("math-installed-type-subset");
  TypeShape shape{TypeShape::Kind::Nominal, 0, type.kind, {}, {}};
  if (auto failure = checkInstalledDomainType(type.identity, shape))
    return failure;
  domains.insert(type.identity);
  return Error::success();
}

Expected<raw::Identity> domainPackage(StringRef name) {
  const auto &catalog = protocol::installedDomains();
  const auto *domain = catalog.domain(name);
  if (!domain)
    return error("math-installed-domain");
  json::Array associated, capabilities, types;
  for (const auto &member : domain->associated)
    associated.push_back(json::Array{member.member, member.identity});
  for (const auto &capability : domain->capabilities)
    capabilities.push_back(capability);
  for (const auto &type : catalog.allLogicalTypes())
    if (type.domain == name) {
      const auto *permissions = protocol::typePermissions(type.kind);
      if (permissions && permissions->copy && permissions->drop &&
          (permissions->custody == protocol::Custody::PublicValue ||
           permissions->custody == protocol::Custody::PrivateImmutable))
        types.push_back(
            json::Array{type.kind, permissions->copy, permissions->drop,
                        permissions->custody == protocol::Custody::PublicValue
                            ? "PublicValue"
                            : "PrivateImmutable"});
    }
  return pin(name,
             json::Array{"domain", "closed-unary-and-field-families/1", name,
                         domain->sort, domain->modulus, std::move(associated),
                         std::move(capabilities), std::move(types)});
}
} // namespace

Expected<Installation>
Installation::create(ArrayRef<protocol::BindingApplication> selected,
                     ArrayRef<std::string> codecs,
                     ArrayRef<protocol::BindingApplication> selectedServices) {
  Installation result;
  std::set<std::string> domains, operationNames, wireNames;
  for (const auto &binding : selected) {
    const auto *parameters = protocol::parameterContract(binding.contract);
    if (!binding.implementation.empty() ||
        protocol::operationPurity(binding.contract) !=
            protocol::OperationPurity::Total ||
        !parameters ||
        parameters->validator != protocol::ParameterValidator::None)
      return error("math-installed-operation-subset");
    auto signature = protocol::resolveBinding(binding, false);
    if (!signature)
      return signature.takeError();
    if (signature->outputs.size() != 1)
      return error("math-installed-operation-subset");
    json::Array arguments, inputs, outputs;
    for (const auto &argument : binding.arguments)
      arguments.push_back(argument);
    for (const auto &type : signature->inputs) {
      if (auto failure = collectType(type, domains))
        return failure;
      inputs.push_back(type.spelling());
    }
    for (const auto &type : signature->outputs) {
      if (auto failure = collectType(type, domains))
        return failure;
      outputs.push_back(type.spelling());
    }
    // Length-delimited JSON arguments avoid ambiguous concatenated names.
    std::string name = binding.contract + "(";
    raw_string_ostream spelling(name);
    spelling << json::Value(json::Array(arguments)) << ")";
    if (!operationNames.insert(name).second)
      return error("math-installed-duplicate-operation");
    auto identity =
        pin(name, json::Array{"operation", "closed-logical/1", binding.contract,
                              std::move(arguments), "Total", std::move(inputs),
                              std::move(outputs)});
    if (!identity)
      return identity.takeError();
    result.packages.operations.push_back(*identity);
    result.operations.push_back(
        {std::move(*identity), binding, std::move(*signature)});
  }
  for (const auto &name : codecs) {
    const auto *codec = protocol::installedDomains().codec(name);
    if (!codec || !wireNames.insert(name).second)
      return error("math-installed-codec");
    const auto *permissions = protocol::typePermissions(codec->kind);
    if (!permissions || permissions->custody != protocol::Custody::PublicValue)
      return error("math-installed-codec-custody");
    auto payload = protocol::applyBoundType(
        codec->kind, codec->domain.empty()
                         ? std::vector<std::string>{}
                         : std::vector<std::string>{codec->domain});
    if (!payload)
      return payload.takeError();
    if (auto failure = collectType(*payload, domains))
      return failure;
    auto identity = pin(name, json::Array{"wire", "installed-payload/1", name,
                                          payload->spelling()});
    if (!identity)
      return identity.takeError();
    result.packages.wires.push_back(*identity);
    const auto *defaultCodec = protocol::installedDomains().defaultCodec(
        payload->kind, payload->identity);
    result.wires.push_back({std::move(*identity),
                            {name, std::move(*payload),
                             defaultCodec && defaultCodec->identity == name}});
  }
  std::set<std::string> serviceNames;
  for (const auto &binding : selectedServices) {
    auto descriptor = protocol::resolveEntropyService(binding);
    if (!descriptor)
      return descriptor.takeError();
    if (auto failure = collectType(descriptor->reply, domains))
      return failure;
    json::Array arguments;
    for (const auto &argument : binding.arguments)
      arguments.push_back(argument);
    std::string name = binding.contract + "(";
    raw_string_ostream spelling(name);
    spelling << json::Value(json::Array(arguments)) << ")";
    if (!serviceNames.insert(name).second)
      return error("math-installed-service-duplicate");
    auto identity = pin(
        name, json::Array{"service", "nullary-entropy/1", binding.contract,
                          std::move(arguments), descriptor->state.spelling(),
                          descriptor->reply.spelling(),
                          descriptor->sampling.domain ==
                                  protocol::SampleDomain::NonzeroField
                              ? "NonzeroField"
                              : "Field"});
    if (!identity)
      return identity.takeError();
    result.packages.services.push_back(*identity);
    result.services.push_back({std::move(*identity), std::move(*descriptor)});
  }
  // Associated nominal references are dependencies even when a particular
  // closed signature does not use them as a value port. Cycles are harmless:
  // each installed domain is visited once.
  std::vector<std::string> pending(domains.begin(), domains.end());
  for (size_t i = 0; i < pending.size(); ++i)
    for (const auto &member :
         protocol::installedDomains().domain(pending[i])->associated)
      if (domains.insert(member.identity).second)
        pending.push_back(member.identity);
  for (const auto &name : domains) {
    auto identity = domainPackage(name);
    if (!identity)
      return identity.takeError();
    result.packages.domains.push_back(std::move(*identity));
  }
  return result;
}

const protocol::BindingApplication *
Installation::binding(const raw::Identity &identity) const {
  for (const auto &operation : operations)
    if (same(operation.identity, identity))
      return &operation.binding;
  return nullptr;
}

const protocol::EntropyService *
Installation::serviceBinding(const raw::Identity &identity) const {
  for (const auto &service : services)
    if (same(service.identity, identity))
      return &service.descriptor;
  return nullptr;
}

const WireRealization *
Installation::wireBinding(const raw::Identity &identity) const {
  for (const auto &wire : wires)
    if (same(wire.identity, identity))
      return &wire.realization;
  return nullptr;
}

Error Installation::identity(Category category, const raw::Identity &identity,
                             const raw::Manifest &manifest) const {
  const auto *entries = &packages.domains;
  switch (category) {
  case Category::Domain:
    break;
  case Category::Operation:
    entries = &packages.operations;
    break;
  case Category::Wire:
    entries = &packages.wires;
    break;
  case Category::Service:
    entries = &packages.services;
    break;
  case Category::Law:
    entries = &packages.laws;
    break;
  }
  if (llvm::none_of(*entries,
                    [&](const auto &entry) { return same(entry, identity); }))
    return error("math-installed-package");
  std::set<std::string> required;
  if (category == Category::Domain) {
    for (const auto &member :
         protocol::installedDomains().domain(identity.name)->associated)
      required.insert(member.identity);
  } else if (category == Category::Operation) {
    for (const auto &operation : operations)
      if (same(operation.identity, identity)) {
        for (const auto &type : operation.signature.inputs)
          if (auto failure = collectType(type, required))
            return failure;
        for (const auto &type : operation.signature.outputs)
          if (auto failure = collectType(type, required))
            return failure;
      }
  } else if (category == Category::Wire) {
    if (auto failure = collectType(wireBinding(identity)->payload, required))
      return failure;
  } else if (category == Category::Service) {
    if (auto failure = collectType(serviceBinding(identity)->reply, required))
      return failure;
  }
  // Dependencies are complete installed identities. Check the transitive
  // domain closure even when the subject never uses the selected package.
  std::vector<std::string> pending(required.begin(), required.end());
  for (size_t i = 0; i < pending.size(); ++i) {
    const auto &name = pending[i];
    const auto installed = llvm::find_if(
        packages.domains, [&](const auto &id) { return id.name == name; });
    if (installed == packages.domains.end() ||
        llvm::none_of(manifest.domains,
                      [&](const auto &id) { return same(id, *installed); }))
      return error("math-installed-prerequisite");
    for (const auto &member :
         protocol::installedDomains().domain(name)->associated)
      if (required.insert(member.identity).second)
        pending.push_back(member.identity);
  }
  return Error::success();
}

Error Installation::domainType(const raw::Identity &id,
                               const TypeShape &shape) const {
  if (auto failure = identity(Category::Domain, id, packages))
    return failure;
  return checkInstalledDomainType(id.name, shape);
}

Expected<protocol::BoundType>
Installation::logicalType(TypeId type, const TypeTable &types,
                          const raw::Manifest &manifest) const {
  if (types.isCondition(type))
    return protocol::BoundType{"bool", "", ""};
  const auto *shape = types.get(type);
  if (!shape || shape->kind != TypeShape::Kind::Nominal || !shape->domain ||
      *shape->domain >= manifest.domains.size())
    return error("math-installed-type-subset");
  const auto &domain = manifest.domains[*shape->domain];
  if (auto failure = domainType(domain, *shape))
    return failure;
  return protocol::applyBoundType(shape->constructor, {domain.name});
}

Expected<OperationFacts>
Installation::operation(const raw::Identity &id, const OperationSignature &sig,
                        const TypeTable &types,
                        const raw::Manifest &manifest) const {
  if (!sig.parameters.empty() || !sig.capabilities.empty())
    return error("math-installed-operation-signature");
  for (const auto &operation : operations) {
    if (!same(id, operation.identity))
      continue;
    if (sig.arguments.size() != operation.signature.inputs.size())
      return error("math-installed-operation-signature");
    for (size_t i = 0; i < sig.arguments.size(); ++i) {
      auto type = logicalType(sig.arguments[i], types, manifest);
      if (!type)
        return type.takeError();
      if (!(*type == operation.signature.inputs[i]))
        return error("math-installed-operation-signature");
    }
    auto type = logicalType(sig.result, types, manifest);
    if (!type)
      return type.takeError();
    if (!(*type == operation.signature.outputs.front()))
      return error("math-installed-operation-signature");
    return OperationFacts{
        *protocol::operationPurity(operation.binding.contract), {}};
  }
  return error("math-installed-operation");
}

Error Installation::wire(const raw::Identity &id, ArrayRef<NormalStatic> params,
                         TypeId type, const TypeTable &types,
                         const raw::Manifest &manifest) const {
  if (!params.empty())
    return error("math-installed-wire-signature");
  for (const auto &wire : wires) {
    if (!same(id, wire.identity))
      continue;
    auto payload = logicalType(type, types, manifest);
    if (!payload)
      return payload.takeError();
    return *payload == wire.realization.payload
               ? Error::success()
               : error("math-installed-wire-signature");
  }
  return error("math-installed-wire");
}

Error Installation::service(const raw::Identity &id,
                            const CapabilitySignature &sig,
                            const TypeTable &types,
                            const raw::Manifest &manifest) const {
  const auto *descriptor = serviceBinding(id);
  if (!descriptor)
    return error("math-installed-service");
  if (!sig.statics.empty() || !sig.arguments.empty())
    return error("math-installed-service-signature");
  auto reply = logicalType(sig.result, types, manifest);
  if (!reply)
    return reply.takeError();
  return *reply == descriptor->reply
             ? Error::success()
             : error("math-installed-service-signature");
}

Error Installation::attributes(const raw::Identity &id,
                               ArrayRef<NormalStatic> params,
                               const json::Value &value) const {
  if (!binding(id) || !params.empty() || !value.getAsObject() ||
      !value.getAsObject()->empty())
    return error("math-installed-attributes");
  return Error::success();
}
} // namespace zkc::mathematical
