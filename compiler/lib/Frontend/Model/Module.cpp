#include "Module.h"
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
  for (DomainId id : t.arguments)
    key += ":" + std::to_string(id.index);
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
  auto [kind, term] = spelling.split(':');
  Type t;
  t.constructor = kind.str();
  if (!term.empty())
    t.arguments.push_back(internDomain(term, scope));
  return intern(std::move(t));
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
  if (t.kind == Type::Kind::Logical)
    return t.constructor +
           (t.arguments.empty() ? "" : ":" + spelling(t.arguments[0]));
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
                            const std::map<DeclId, DomainId> &sub) {
  auto d = domains.at(id.index);
  if (d.kind == Domain::Kind::Parameter) {
    auto it = sub.find(d.parameter);
    return it == sub.end() ? id : it->second;
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
TypeId Module::substitute(TypeId id, const std::map<DeclId, DomainId> &sub) {
  auto t = types.at(id.index);
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
  if (types.at(port.type.index).kind == Type::Kind::Logical)
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
