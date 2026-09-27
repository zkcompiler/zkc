#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Implementations.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/ResourceUnit.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
#include <map>

using namespace llvm;
namespace zkc::protocol {
namespace {
bool name(StringRef value) {
  return !value.empty() && value.size() <= 256 &&
         (isAlpha(value.front()) || value.front() == '_') &&
         all_of(value, [](char c) {
           return isAlnum(c) || c == '_' || c == '.' || c == '-' || c == '/';
         });
}

} // namespace

StringRef defaultCodec(const BoundType &logical) {
  if (!logical.representation.empty())
    return {};
  const auto *codec =
      installedDomains().defaultCodec(logical.kind, logical.identity);
  return codec ? StringRef(codec->identity) : StringRef{};
}

StringRef installedIdentitySort(StringRef identity) {
  return installedDomains().identitySort(identity);
}
bool staticIdentityMatches(StringRef sort, StringRef identity) {
  if (sort == "Type") {
    auto parsed = parseBoundType(identity, false);
    if (!parsed) {
      consumeError(parsed.takeError());
      return false;
    }
    return true;
  }
  if (sort == "Nat") {
    uint64_t value;
    return !identity.empty() &&
           !(identity.size() > 1 && identity.front() == '0') &&
           all_of(identity, [](char c) { return isDigit(c); }) &&
           !identity.getAsInteger(10, value) && value <= 1048576;
  }
  return !sort.empty() && installedIdentitySort(identity) == sort;
}
StringRef associatedIdentity(StringRef identity, StringRef key) {
  return installedDomains().associatedIdentity(identity, key);
}

bool isDiagonalRepresentation(StringRef representation) {
  for (const auto &entry : installedImplementations().all())
    for (const auto &override : entry.representations)
      if (override.identity == representation) {
        const auto *rep = installedDomains().representation(
            override.kind, override.domain, override.identity);
        if (rep && rep->layout == "diagonal")
          return true;
      }
  return false;
}

Expected<std::string> defaultImplementation(const BindingApplication &binding) {
  auto logical = resolveBinding(binding, false);
  if (!logical)
    return logical.takeError();
  if (resourceUnitContract(binding.contract))
    return "logical/" + binding.contract;
  auto implementation = installedImplementations().defaultFor(binding);
  if (!implementation)
    return implementation.takeError();
  auto selected = binding;
  selected.implementation = (*implementation)->identity;
  auto physical = resolveBinding(selected, true);
  if (!physical)
    return physical.takeError();
  return selected.implementation;
}

Error checkImplementation(StringRef contract, StringRef implementation) {
  if (resourceUnitContract(contract))
    return implementation == ("logical/" + contract).str()
               ? Error::success()
               : error("binding-implementation");
  if (none_of(boundOperationContracts(),
              [&](const auto &op) { return op.name == contract; }))
    return error("binding-contract");
  return installedImplementations().find(contract, implementation)
             ? Error::success()
             : error("binding-implementation");
}

Error checkStaticVocabulary(const generic::Signature &signature) {
  for (const auto &sort : signature.scope.sorts)
    if (sort != "Type" && sort != "Nat" && !is_contained(domainSorts(), sort))
      return error("generic-declared-sort");
  for (const auto &predicate : signature.requirements) {
    if (predicate.kind == requirements::Predicate::Kind::Equal)
      continue; // Equality formation, including sort agreement, is generic.
    const CapabilityDeclaration *declaration = nullptr;
    for (const auto &candidate : capabilityDeclarations())
      if (candidate.name == predicate.relation) {
        declaration = &candidate;
        break;
      }
    if (!declaration)
      return error("generic-declared-predicate");
    if (declaration->parameters.size() != predicate.arguments.size())
      return error("generic-predicate-arity");
    for (auto [index, parameter] :
         zip(predicate.arguments, declaration->parameters))
      if (index >= signature.scope.sorts.size() ||
          signature.scope.sorts[index] !=
              (parameter.kind == StaticKind::Domain ? parameter.sort
               : parameter.kind == StaticKind::Type ? "Type"
                                                    : "Nat"))
        return error("generic-predicate-sort");
  }
  return Error::success();
}

Expected<std::vector<std::string>>
resolveStaticArguments(const generic::Scope &scope,
                       ArrayRef<std::string> arguments) {
  if (scope.terms.size() != scope.sorts.size() || scope.terms.size() > 128)
    return error("binding-static-scope");
  std::vector<std::string> selected;
  size_t next = 0;
  for (auto [i, term] : enumerate(scope.terms)) {
    std::string identity;
    if (term.arguments) {
      if (term.parent || scope.constants.count(i) || scope.sorts[i] != "Type")
        return error("binding-static-scope");
      std::vector<std::string> args;
      for (unsigned argument : *term.arguments) {
        if (argument >= i)
          return error("binding-static-scope");
        args.push_back(selected[argument]);
      }
      auto type = applyBoundType(term.name, args);
      if (!type)
        return type.takeError();
      identity = type->spelling();
    } else if (term.parent) {
      if (*term.parent >= i)
        return error("binding-static-scope");
      identity = installedDomains()
                     .associatedIdentity(selected[*term.parent], term.name)
                     .str();
    } else if (auto fixed = scope.constants.find(i);
               fixed != scope.constants.end()) {
      identity = fixed->second;
    } else {
      if (next >= arguments.size())
        return error("binding-static-arity");
      identity = arguments[next++];
    }
    if (identity.empty())
      return error("binding-static-identity");
    if (scope.sorts[i] == "Type") {
      auto type = parseBoundType(identity, false);
      if (!type)
        return type.takeError();
    } else if (scope.sorts[i] == "Nat") {
      StringRef value = identity;
      uint64_t n;
      if ((value.size() > 1 && value.front() == '0') ||
          !all_of(value, [](char c) { return isDigit(c); }) ||
          value.getAsInteger(10, n) || n > 1048576)
        return error("binding-static-identity");
    } else if (installedDomains().identitySort(identity) != scope.sorts[i])
      return error("binding-static-identity");
    selected.push_back(std::move(identity));
  }
  if (next != arguments.size())
    return error("binding-static-arity");
  return selected;
}

Error checkClosedRequirements(ArrayRef<requirements::Predicate> predicates,
                              ArrayRef<std::string> selected) {
  for (const auto &p : predicates) {
    std::vector<std::string> arguments;
    for (unsigned i : p.arguments) {
      if (i >= selected.size())
        return error("binding-static-scope");
      arguments.push_back(selected[i]);
    }
    if (p.kind == requirements::Predicate::Kind::Equal
            ? arguments.size() != 2 || arguments[0] != arguments[1]
            : !installedDomains().hasFact(p.relation, arguments))
      return error("binding-requirement");
  }
  return Error::success();
}

Expected<BoundOperation> resolveBinding(const BindingApplication &binding,
                                        bool physical) {
  if (physical && binding.implementation.empty())
    return error("binding-stage");
  if (!physical && !binding.implementation.empty()) {
    // A source may constrain future implementation selection without lowering
    // its logical ports. Validate that exact choice independently here.
    auto selected = resolveBinding(binding, true);
    if (!selected)
      return selected.takeError();
  }
  if (resourceUnitContract(binding.contract)) {
    if (binding.arguments.size() != 1 ||
        !resourceUnitDomain(binding.arguments[0]))
      return error("binding-resource-unit-domain");
    if (physical && binding.implementation != "logical/" + binding.contract)
      return error("binding-implementation");
    BoundType ty{"resource_unit", binding.arguments[0],
                 physical ? "logical.resource_unit/1" : ""};
    return BoundOperation{binding.contract == "resource_unit.create"
                              ? std::vector<BoundType>{}
                              : std::vector<BoundType>{ty},
                          binding.contract == "resource_unit.consume"
                              ? std::vector<BoundType>{}
                              : std::vector<BoundType>{ty}};
  }
  // This is a physical adapter contract, not a generic logical primitive. Its
  // implementation must execute and account for the representation conversion.
  if (binding.contract == "table.relayout") {
    if (!physical || binding.arguments.size() != 3 ||
        installedDomains().identitySort(binding.arguments[0]) != "Field" ||
        binding.implementation != "arkworks/table.relayout")
      return error("binding-conversion");
    auto from = parseBoundType(
        "table:" + binding.arguments[0] + "@" + binding.arguments[1], true);
    if (!from)
      return from.takeError();
    auto to = parseBoundType(
        "table:" + binding.arguments[0] + "@" + binding.arguments[2], true);
    if (!to)
      return to.takeError();
    if (*from == *to)
      return error("binding-conversion");
    return BoundOperation{{*from}, {*to}};
  }
  const generic::Signature *signature = nullptr;
  for (const auto &op : boundOperationContracts())
    if (op.name == binding.contract)
      signature = &op.signature;
  if (!signature)
    return error("binding-contract");
  auto identities = resolveStaticArguments(signature->scope, binding.arguments);
  if (!identities)
    return identities.takeError();
  if (auto e = checkClosedRequirements(signature->requirements, *identities))
    return e;
  const ImplementationDescriptor *implementation = nullptr;
  if (physical) {
    implementation = installedImplementations().find(binding.contract,
                                                     binding.implementation);
    if (!implementation)
      return error("binding-implementation");
    if (auto e = checkImplementationArguments(*implementation, signature->scope,
                                              *identities))
      return e;
  }
  BoundOperation result;
  auto type = [&](const generic::Type &t) -> Expected<BoundType> {
    std::vector<std::string> args;
    for (unsigned argument : t.arguments) {
      if (argument >= identities->size())
        return error("binding-static-scope");
      args.push_back((*identities)[argument]);
    }
    auto application = applyBoundType(t.constructor, args);
    if (!application)
      return application.takeError();
    BoundType logical = std::move(*application);
    if (!physical)
      return logical;
    return defaultRepresentation(logical);
  };
  for (const auto &t : signature->inputs) {
    auto selected = type(t);
    if (!selected)
      return selected.takeError();
    result.inputs.push_back(std::move(*selected));
  }
  for (const auto &t : signature->outputs) {
    auto selected = type(t);
    if (!selected)
      return selected.takeError();
    result.outputs.push_back(std::move(*selected));
  }
  if (implementation)
    if (auto e = applyImplementationRepresentations(*implementation, result))
      return e;
  return result;
}

Error checkBindingDeclaration(StringRef symbol,
                              const BindingApplication &binding,
                              bool physical) {
  if (!name(symbol) || symbol.find('/') != std::string::npos)
    return error("binding-name");
  if (binding.arguments.size() > 128)
    return error("binding-static-arity");
  // The declaration checks kind and canonical form. Type/Nat arguments are
  // not restricted to the lexical grammar of nominal domain identities.
  auto resolved = resolveBinding(binding, physical);
  return resolved ? Error::success() : resolved.takeError();
}

} // namespace zkc::protocol
