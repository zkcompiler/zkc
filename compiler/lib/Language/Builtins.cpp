#include "zkc/Language/Builtins.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language {
namespace {
using K = Type::Kind;
bool dataConstructor(StringRef name) {
  // Managed services and source nominal representations have separate owners.
  // These are native data representations, including runtime polynomial data;
  // formal polynomials are a distinct mathematical type.
  return name == "vector" || name == "matrix" || name == "groups" ||
         name == "indices" || name == "polynomial" || name == "table" ||
         name == "point" || name == "round" || name == "sequence" ||
         name == "field_array";
}
} // namespace
bool isDomainSort(StringRef sort) {
  return llvm::is_contained(protocol::domainSorts(), sort);
}
Expected<Type> domainMember(const Type &base, StringRef member) {
  auto members = protocol::associatedMemberDeclarations();
  auto found = llvm::find_if(members, [&](const auto &entry) {
    return entry.owner.sort == domainSort(base) && entry.name == member;
  });
  if (found == members.end() ||
      found->result.kind != protocol::StaticKind::Domain ||
      !isDomainSort(found->result.sort))
    return error("source.type",
                 "domain has no installed association: " + member);
  auto identity = base.symbolic ? base.domain + "::" + member.str()
                                : protocol::installedDomains()
                                      .associatedIdentity(base.domain, member)
                                      .str();
  if (identity.empty())
    return error("source.type", "domain association is unavailable: " + member);
  auto result = domainType(found->result.sort, identity);
  if (base.symbolic) {
    result.symbolic = true;
    result.arguments = {base};
    if (!isStaticOnly(result))
      result.assumptions = {true, true, false, false};
  }
  return result;
}
bool isNativeData(const Type &type) {
  return type.kind == K::Field || type.kind == K::Group ||
         type.kind == K::Boolean || type.kind == K::Index ||
         type.kind == K::Builtin;
}
Expected<std::string> kernelArgument(const Type &type, StringRef sort) {
  if (type.symbolic)
    return error("source.builtin", "installed binding requires closed statics");
  if (sort == "Type") {
    auto layout = builtinLayout(type);
    if (!layout)
      return layout.takeError();
    return layout->spelling();
  }
  if (sort == "Nat") {
    if (type.kind != K::Natural || !type.dimension.isClosed() ||
        type.dimension.closedValue() > 1048576)
      return error("source.builtin", "native natural is outside 0..1048576");
    return std::to_string(type.dimension.closedValue());
  }
  if (isDomainSort(sort) && domainSort(type) == sort) {
    if (!protocol::staticIdentityMatches(sort, type.domain))
      return error("source.builtin", "uninstalled domain identity");
    return type.domain;
  }
  return error("source.builtin", "installed static argument sort differs");
}
Expected<Type> formalType(StringRef name, ArrayRef<Type> arguments) {
  if (name != "polynomial" || arguments.size() != 2 ||
      arguments[0].kind != K::Field || arguments[1].kind != K::Natural)
    return error("source.formal",
                 "formal polynomial requires a field and natural arity");
  Type result(K::Formal, name.str());
  result.arguments.assign(arguments.begin(), arguments.end());
  return result;
}
Expected<Type> builtinType(StringRef name, ArrayRef<Type> arguments) {
  if (name == "bool" && arguments.empty())
    return Type{};
  if (name == "index" && arguments.empty())
    return Type(K::Index);
  if (arguments.size() == 1 &&
      ((name == "field" && arguments[0].kind == K::Field) ||
       (name == "group" && arguments[0].kind == K::Group)))
    return arguments[0];
  const auto *constructor = protocol::typeDeclaration(name);
  if (!dataConstructor(name) || !constructor)
    return error("source.builtin",
                 "constructor is not an admitted native data type");
  if (arguments.size() != constructor->parameters.size())
    return error("source.builtin", "native type argument count differs");
  for (unsigned i = 0; i < arguments.size(); ++i) {
    const auto &argument = arguments[i];
    const auto &parameter = constructor->parameters[i];
    using S = protocol::StaticKind;
    bool formed = parameter.kind == S::Type ? isNativeData(argument)
                  : parameter.kind == S::Nat
                      ? argument.kind == K::Natural
                      : domainSort(argument) == parameter.sort &&
                            isDomainSort(parameter.sort);
    if (!formed)
      return error("source.builtin",
                   "native type argument sort or representation differs");
    if (parameter.kind == S::Nat && argument.dimension.isClosed() &&
        argument.dimension.closedValue() > 1048576)
      return error("source.builtin", "native natural is outside 0..1048576");
  }
  Type result(K::Builtin, name.str());
  result.arguments.assign(arguments.begin(), arguments.end());
  return result;
}
Expected<protocol::BoundType> builtinLayout(const Type &type) {
  if (type.symbolic)
    return error("source.builtin", "native data layout requires a closed type");
  if (type.kind == K::Boolean)
    return protocol::parseBoundType("bool", false);
  if (type.kind == K::Index)
    return protocol::parseBoundType("index", false);
  if (type.kind == K::Field || type.kind == K::Group)
    return protocol::parseBoundType(
        (type.kind == K::Field ? "field:" : "group:") + type.domain, false);
  if (type.kind != K::Builtin)
    return error("source.builtin",
                 "source nominal or product requires its own layout");
  auto formed = builtinType(type.domain, type.arguments);
  if (!formed)
    return formed.takeError();
  const auto *constructor = protocol::typeDeclaration(type.domain);
  std::vector<std::string> arguments;
  for (unsigned i = 0; i < type.arguments.size(); ++i) {
    const auto &parameter = constructor->parameters[i];
    auto argument = kernelArgument(
        type.arguments[i], parameter.kind == protocol::StaticKind::Type ? "Type"
                           : parameter.kind == protocol::StaticKind::Nat
                               ? "Nat"
                               : parameter.sort);
    if (!argument)
      return argument.takeError();
    arguments.push_back(std::move(*argument));
  }
  return protocol::applyBoundType(type.domain, arguments);
}
Expected<std::vector<std::string>> kernelArguments(StringRef contract,
                                                   ArrayRef<Type> arguments) {
  auto operations = protocol::executableOperationContracts();
  auto found = llvm::find_if(operations, [&](const auto &operation) {
    return operation.name == contract;
  });
  if (found == operations.end())
    return error("source.kernel", "unknown installed operation");
  std::vector<std::string> result;
  const auto &scope = found->signature.scope;
  for (unsigned i = 0; i < scope.terms.size(); ++i) {
    const auto &term = scope.terms[i];
    if (term.parent || term.arguments || scope.constants.count(i))
      continue;
    if (result.size() >= arguments.size())
      return error("source.kernel", "installed static argument count differs");
    auto value = kernelArgument(arguments[result.size()], scope.sorts[i]);
    if (!value)
      return value.takeError();
    result.push_back(std::move(*value));
  }
  if (result.size() != arguments.size())
    return error("source.kernel", "installed static argument count differs");
  return result;
}
} // namespace zkc::language
