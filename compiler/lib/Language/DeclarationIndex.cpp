#include "zkc/Language/DeclarationIndex.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language {
DeclarationIndex::DeclarationIndex(ArrayRef<Declaration> declarations,
                                   ArrayRef<SourceBuffer> sources,
                                   std::vector<Namespace> namespaces)
    : namespaces(std::move(namespaces)) {
  for (const auto &decl : declarations) {
    parents.push_back(decl.parent);
    canonicalDeclarations.emplace(decl.qualifiedName, decl.id);
    if (decl.kind == Declaration::Kind::Module)
      moduleMembers.emplace(decl.id.index, decl.members);
    if (decl.kind == Declaration::Kind::Record ||
        decl.kind == Declaration::Kind::Variant ||
        decl.kind == Declaration::Kind::Associated)
      nominalHomes.emplace(decl.qualifiedName, decl.module);
    if (decl.span.source.index >= sources.size() ||
        sources[decl.span.source.index].origin != SourceOrigin::Installation)
      continue;
    if (auto *row = protocol::frontendDeclaration(decl.qualifiedName)) {
      associations.emplace(decl.id.index, row);
      if (row->implicit)
        implicitDeclarations.emplace(row->name, decl.id);
    }
  }
  for (const auto &row : protocol::frontendHomes()) {
    auto module = canonical(row.module);
    if (module &&
        declarations[module->index].kind == Declaration::Kind::Module) {
      constructorHomes.emplace(row.constructor, *module);
      for (const auto &member : row.members) {
        auto target = canonical(member);
        if (!target || module->index >= this->namespaces.size())
          continue;
        const auto &decl = declarations[target->index];
        auto at = this->namespaces[module->index].find(decl.name);
        if (at != this->namespaces[module->index].end() &&
            at->second.declaration.index == target->index &&
            at->second.isPublic && decl.isPublic &&
            !llvm::any_of(moduleMembers[module->index],
                          [&](auto id) { return id.index == target->index; }))
          moduleMembers[module->index].push_back(*target);
      }
    }
  }
}
std::optional<DeclarationId> DeclarationIndex::lookup(DeclarationId context,
                                                      StringRef name) const {
  bool absolute = name.consume_front("::");
  auto [head, tail] = name.split("::");
  std::optional<DeclarationId> selected;
  if (!absolute && context.index < parents.size()) {
    for (auto scope = std::optional(context); scope;
         scope = parents[scope->index]) {
      if (scope->index >= namespaces.size())
        return {};
      auto at = namespaces[scope->index].find(head.str());
      if (at != namespaces[scope->index].end()) {
        selected = at->second.declaration;
        break;
      }
    }
  }
  if (!selected) {
    auto prefix = name;
    while (!prefix.empty()) {
      auto id = canonical(prefix);
      if (id && !parents[id->index] && moduleMembers.count(id->index)) {
        selected = id;
        tail = name.size() == prefix.size()
                   ? StringRef{}
                   : name.drop_front(prefix.size() + 2);
        break;
      }
      prefix = prefix.contains("::") ? prefix.rsplit("::").first : StringRef{};
    }
  }
  if (!selected && tail.empty() && !absolute)
    return implicit(name);
  while (selected && !tail.empty()) {
    auto next = tail.split("::");
    if (selected->index >= namespaces.size())
      return {};
    auto at = namespaces[selected->index].find(next.first.str());
    if (at == namespaces[selected->index].end())
      return {};
    selected = at->second.declaration;
    tail = next.second;
  }
  return selected;
}
const protocol::FrontendDeclaration *
DeclarationIndex::association(DeclarationId id) const {
  auto at = associations.find(id.index);
  return at == associations.end() ? nullptr : at->second;
}
std::optional<DeclarationId> DeclarationIndex::implicit(StringRef name) const {
  auto at = implicitDeclarations.find(name.str());
  return at == implicitDeclarations.end() ? std::nullopt
                                          : std::optional(at->second);
}
std::optional<DeclarationId> DeclarationIndex::canonical(StringRef name) const {
  auto at = canonicalDeclarations.find(name.str());
  return at == canonicalDeclarations.end() ? std::nullopt
                                           : std::optional(at->second);
}
std::optional<DeclarationId> DeclarationIndex::home(const Type &type) const {
  if (type.kind == Type::Kind::Module)
    return {};
  if (type.kind == Type::Kind::Record ||
      type.kind == Type::Kind::LogicalRecord ||
      type.kind == Type::Kind::Variant || type.kind == Type::Kind::Associated) {
    auto at = nominalHomes.find(type.domain);
    return at == nominalHomes.end() ? std::nullopt : std::optional(at->second);
  }
  // Builtin.domain is the checked catalog constructor identity. Domain names
  // of field/group types and printed aliases are never home lookup keys.
  StringRef head = type.kind == Type::Kind::Builtin  ? StringRef(type.domain)
                   : type.kind == Type::Kind::Oracle ? "oracle"
                   : type.kind == Type::Kind::OracleSequence ? "oracle_sequence"
                                                             : StringRef{};
  auto at = constructorHomes.find(head.str());
  return at == constructorHomes.end() ? std::nullopt
                                      : std::optional(at->second);
}
ArrayRef<DeclarationId> DeclarationIndex::members(DeclarationId module) const {
  auto at = moduleMembers.find(module.index);
  return at == moduleMembers.end() ? ArrayRef<DeclarationId>{}
                                   : ArrayRef<DeclarationId>(at->second);
}
} // namespace zkc::language
