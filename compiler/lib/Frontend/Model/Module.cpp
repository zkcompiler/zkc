#include "Module.h"
#include "../Static/Structural.h"
#include "zkc/Contracts/Bindings.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include <functional>

using namespace llvm;
namespace zkc::frontend::model {
Module::Module() { addScope({}, {}); }
ScopeId Module::addScope(ScopeId parent, DeclId owner) {
  ScopeId id{uint32_t(scopes.size())};
  scopes.push_back({id, parent, owner});
  return id;
}
DeclId Module::add(Declaration::Kind kind, ScopeId scope, StringRef name,
                   std::optional<source::Span> location) {
  DeclId id{uint32_t(declarations.size())};
  Declaration d;
  d.id = id;
  d.kind = kind;
  d.scope = scope;
  d.name = name.str();
  d.location = location;
  d.members = addScope(scope, id);
  declarations.push_back(std::move(d));
  names.emplace(std::make_pair(scope, name.str()), id);
  return id;
}
DeclId Module::lookup(ScopeId scope, StringRef name) const {
  auto it = names.find({scope, name.str()});
  return it == names.end() ? DeclId{} : it->second;
}
DomainId Module::internDomain(StringRef term, ScopeId scope, StringRef sort) {
  Domain d;
  d.name = term.str();
  d.sort = sort.str();
  DeclId parameter = lookup(scope, term);
  if (parameter.valid() &&
      declarations[parameter.index].kind == Declaration::Kind::Parameter) {
    d.kind = Domain::Kind::Parameter;
    d.parameter = parameter;
    d.sort = declarations[parameter.index].sort;
  } else if (auto installed = protocol::installedIdentitySort(term);
             !installed.empty()) {
    d.sort = installed.str();
  } else {
    auto [root, member] = term.rsplit('.');
    if (!root.empty() && root != term && !member.empty()) {
      d.kind = Domain::Kind::Projection;
      d.name = member.str();
      d.parent = internDomain(root, scope);
      auto associated =
          protocol::associatedIdentity(spelling(d.parent), member);
      if (!associated.empty())
        return internDomain(associated, scope);
      d.sort =
          protocol::associatedMemberSort(domains[d.parent.index].sort, member)
              .str();
    }
  }
  std::string key = std::to_string(unsigned(d.kind)) + ":" + d.name + ":" +
                    std::to_string(d.parameter.index) + ":" +
                    std::to_string(d.parent.index);
  auto found = domainKeys.find(key);
  if (found != domainKeys.end())
    return found->second;
  DomainId id{uint32_t(domains.size())};
  domains.push_back(std::move(d));
  domainKeys.emplace(std::move(key), id);
  return id;
}
TypeId Module::intern(Type t) {
  std::string key = std::to_string(unsigned(t.kind)) + ":" + t.constructor +
                    ":" + std::to_string(t.declaration.index) +
                    ":count:" + std::to_string(t.count);
  for (const auto &a : t.arguments)
    key += ":argument:" + std::to_string(unsigned(a.kind)) + ":" +
           std::to_string(a.domain.index) + ":" + std::to_string(a.type.index) +
           ":" + std::to_string(a.parameter.index) + ":" +
           std::to_string(a.number);
  for (TypeId id : t.elements)
    key += ":element:" + std::to_string(id.index);
  auto it = typeKeys.find(key);
  if (it != typeKeys.end())
    return it->second;
  TypeId id{uint32_t(types.size())};
  types.push_back(std::move(t));
  typeKeys.emplace(std::move(key), id);
  return id;
}
TypeId Module::logical(StringRef spelling, ScopeId scope) {
  Type t;
  auto parameter = lookup(scope, spelling);
  if (parameter.valid() && declarations[parameter.index].sort == "Type") {
    t.kind = Type::Kind::Parameter;
    t.declaration = parameter;
    return intern(std::move(t));
  }
  auto parsed = splitLogical(spelling);
  if (!parsed)
    return {};
  t.constructor = parsed->constructor;
  const auto *declaration = protocol::typeDeclaration(t.constructor);
  if (!declaration) {
    // Core carriers such as variants have their own common reader.
    auto carrier = protocol::parseBoundType(spelling, false);
    if (!carrier) {
      consumeError(carrier.takeError());
      diagnostics.push_back(
          {"source-type",
           "unknown logical constructor '" + t.constructor + "'",
           {}});
      return {};
    }
  } else if (declaration->common &&
             parsed->arguments.size() != declaration->parameters.size()) {
    diagnostics.push_back(
        {"source-type-arity", "wrong number of logical type arguments", {}});
    return {};
  }
  for (size_t i = 0; i < parsed->arguments.size(); ++i) {
    std::string sort;
    if (declaration && i < declaration->parameters.size()) {
      const auto &p = declaration->parameters[i];
      sort = p.kind == protocol::StaticKind::Type  ? "Type"
             : p.kind == protocol::StaticKind::Nat ? "Nat"
                                                   : p.sort;
    }
    auto actual = argument(parsed->arguments[i], sort, scope);
    if ((actual.kind == StaticArgument::Kind::Type && !actual.type.valid()) ||
        (actual.kind == StaticArgument::Kind::Domain && !actual.domain.valid()))
      return {};
    t.arguments.push_back(actual);
  }
  return intern(std::move(t));
}
StaticArgument Module::argument(StringRef value, StringRef sort,
                                ScopeId scope) {
  if (sort == "Type")
    return StaticArgument::typeOf(logical(value, scope));
  if (sort == "Nat") {
    auto parameter = lookup(scope, value);
    if (parameter.valid() && declarations[parameter.index].sort == "Nat")
      return StaticArgument::natural(0, parameter);
    uint64_t number = 0;
    if (value.getAsInteger(10, number) || number > 1048576) {
      diagnostics.push_back(
          {"source-static-sort",
           "expected a bounded natural or a scoped Nat parameter",
           {}});
      return {};
    }
    return StaticArgument::natural(number);
  }
  return internDomain(value, scope, sort);
}
bool Module::checkArgument(DeclId parameter, const StaticArgument &argument) {
  const auto &p = declarations.at(parameter.index);
  bool valid = false;
  if (p.sort == "Type")
    valid = argument.kind == StaticArgument::Kind::Type &&
            argument.type.index < types.size();
  else if (p.sort == "Nat")
    valid = argument.kind == StaticArgument::Kind::Natural &&
            (argument.parameter.valid()
                 ? argument.parameter.index < declarations.size() &&
                       declarations[argument.parameter.index].sort == "Nat"
                 : argument.number <= 1048576);
  else
    valid = argument.kind == StaticArgument::Kind::Domain &&
            argument.domain.index < domains.size() &&
            domains[argument.domain.index].sort == p.sort;
  if (!valid)
    diagnostics.push_back(
        {"source-static-sort",
         "substitution has the wrong kind or sort for '" + p.name + "'",
         p.location});
  return valid;
}
std::string Module::spelling(const StaticArgument &a) const {
  switch (a.kind) {
  case StaticArgument::Kind::Domain:
    return spelling(a.domain);
  case StaticArgument::Kind::Type:
    return spelling(a.type);
  case StaticArgument::Kind::Natural:
    return a.parameter.valid() ? declarations.at(a.parameter.index).name
                               : std::to_string(a.number);
  }
  llvm_unreachable("unknown static argument kind");
}
StaticArgument Module::substitute(const StaticArgument &a,
                                  const std::map<DeclId, StaticArgument> &sub) {
  switch (a.kind) {
  case StaticArgument::Kind::Domain:
    return substitute(a.domain, sub);
  case StaticArgument::Kind::Type:
    return StaticArgument::typeOf(substitute(a.type, sub));
  case StaticArgument::Kind::Natural:
    if (auto it = sub.find(a.parameter); a.parameter.valid() && it != sub.end())
      return checkArgument(a.parameter, it->second) ? it->second : a;
    return a;
  }
  llvm_unreachable("unknown static argument kind");
}
TypeId Module::record(DeclId declaration, ArrayRef<std::string> arguments,
                      ScopeId scope) {
  Type t;
  t.kind = Type::Kind::Record;
  t.declaration = declaration;
  for (const auto &argument : arguments)
    t.arguments.push_back(internDomain(argument, scope));
  return intern(std::move(t));
}
TypeId Module::product(ArrayRef<TypeId> elements) {
  Type t;
  t.kind = Type::Kind::Product;
  t.elements.assign(elements.begin(), elements.end());
  auto id = intern(std::move(t));
  std::vector<Port> flat;
  for (auto [i, element] : enumerate(elements)) {
    auto fields = leaves({std::to_string(i), {}, element, {}});
    flat.insert(flat.end(), fields.begin(), fields.end());
  }
  layouts[id] = std::move(flat);
  return id;
}
TypeId Module::array(TypeId element, uint64_t count) {
  Type t;
  t.kind = Type::Kind::Array;
  t.elements = {element};
  t.count = count;
  auto id = intern(std::move(t));
  std::vector<Port> flat;
  for (uint64_t i = 0; i < count; ++i) {
    auto fields = leaves({std::to_string(i), {}, element, {}});
    flat.insert(flat.end(), fields.begin(), fields.end());
  }
  layouts[id] = std::move(flat);
  return id;
}
std::string Module::spelling(DomainId id) const {
  const auto &d = domains.at(id.index);
  if (d.kind == Domain::Kind::Projection)
    return spelling(d.parent) + "." + d.name;
  return d.name;
}
std::string Module::spelling(TypeId id) const {
  const auto &t = types.at(id.index);
  if (t.kind == Type::Kind::Parameter)
    return declarations.at(t.declaration.index).name;
  if (t.kind == Type::Kind::Logical) {
    std::vector<std::string> arguments;
    for (const auto &argument : t.arguments)
      arguments.push_back(spelling(argument));
    return logicalSpelling(t.constructor, arguments);
  }
  if (t.kind == Type::Kind::Array)
    return "Array<" + spelling(t.elements.front()) + ", " +
           std::to_string(t.count) + ">";
  if (t.kind == Type::Kind::Product) {
    std::string result = "(";
    for (auto [i, element] : enumerate(t.elements)) {
      if (i)
        result += ", ";
      result += spelling(element);
    }
    if (t.elements.size() == 1)
      result += ",";
    return result + ")";
  }
  std::string result = declarations.at(t.declaration.index).name;
  if (!t.arguments.empty()) {
    result += "<";
    for (auto argument : t.arguments) {
      if (result.back() != '<')
        result += ", ";
      result += spelling(argument);
    }
    result += ">";
  }
  return result;
}
DomainId Module::substitute(DomainId id,
                            const std::map<DeclId, StaticArgument> &sub) {
  auto d = domains.at(id.index);
  if (d.kind == Domain::Kind::Parameter) {
    auto it = sub.find(d.parameter);
    return it == sub.end() || !checkArgument(d.parameter, it->second)
               ? id
               : it->second.domain;
  }
  if (d.kind != Domain::Kind::Projection)
    return id;
  auto parent = substitute(d.parent, sub);
  if (parent == d.parent)
    return id;
  auto identity = protocol::associatedIdentity(spelling(parent), d.name);
  if (!identity.empty())
    return internDomain(identity, {0});
  // Preserve parameter identity when the projection is still abstract.
  d.parent = parent;
  std::string key = std::to_string(unsigned(d.kind)) + ":" + d.name + ":" +
                    std::to_string(d.parameter.index) + ":" +
                    std::to_string(parent.index);
  auto it = domainKeys.find(key);
  if (it != domainKeys.end())
    return it->second;
  DomainId result{uint32_t(domains.size())};
  domains.push_back(std::move(d));
  domainKeys.emplace(std::move(key), result);
  return result;
}
TypeId Module::substitute(TypeId id,
                          const std::map<DeclId, StaticArgument> &sub) {
  auto t = types.at(id.index);
  if (t.kind == Type::Kind::Parameter) {
    auto it = sub.find(t.declaration);
    return it == sub.end() || !checkArgument(t.declaration, it->second)
               ? id
               : it->second.type;
  }
  if (t.kind == Type::Kind::Array)
    return array(substitute(t.elements.front(), sub), t.count);
  if (t.kind == Type::Kind::Product) {
    for (auto &element : t.elements)
      element = substitute(element, sub);
    return product(t.elements);
  }
  for (auto &argument : t.arguments)
    argument = substitute(argument, sub);
  auto result = intern(std::move(t));
  if (result != id && layouts.count(id) && !layouts.count(result)) {
    auto layout = layouts.at(id);
    for (auto &field : layout)
      field.type = substitute(field.type, sub);
    layouts[result] = std::move(layout);
  }
  return result;
}
std::vector<Port> Module::leaves(const Port &port) const {
  if (types.at(port.type.index).kind == Type::Kind::Logical ||
      types.at(port.type.index).kind == Type::Kind::Parameter)
    return {port};
  auto result = layouts.at(port.type);
  for (auto &leaf : result) {
    leaf.name = port.name.empty() ? leaf.name : port.name + "." + leaf.name;
    leaf.role = port.role;
  }
  return result;
}

bool Module::containsChecked(TypeId id) const {
  const auto &t = types.at(id.index);
  if (t.kind == Type::Kind::Product || t.kind == Type::Kind::Array)
    return llvm::any_of(t.elements,
                        [&](TypeId e) { return containsChecked(e); });
  if (t.kind != Type::Kind::Record)
    return false;
  const auto &d = declarations.at(t.declaration.index);
  if (d.checked)
    return true;
  return llvm::any_of(d.fields,
                      [&](const Port &f) { return containsChecked(f.type); });
}
} // namespace zkc::frontend::model
