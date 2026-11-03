#include "zkc/Language/DeclarationIndex.h"
#include "llvm/ADT/STLExtras.h"
#include <cassert>
#include <set>
using namespace llvm;
namespace zkc::language {
namespace {
ResolutionCategory category(const Declaration &decl) {
  using K = Declaration::Kind;
  switch (decl.kind) {
  case K::Module:
    return ResolutionCategory::Module;
  case K::Interface:
    return ResolutionCategory::Interface;
  case K::Domain:
    return ResolutionCategory::Domain;
  case K::Record:
  case K::Variant:
  case K::Alias:
  case K::Associated:
    return ResolutionCategory::Type;
  case K::Math:
  case K::Local:
  case K::Protocol:
  case K::Oracle:
  case K::DomainFunction:
  case K::EntryFunction:
    return ResolutionCategory::Callable;
  default:
    return ResolutionCategory::Other;
  }
}
bool charge(const LookupTraversal &traversal) {
  return !traversal.charge || traversal.charge();
}
} // namespace
bool DeclarationIndex::add(const Declaration &decl, SourceOrigin origin) {
  assert(!frozen && decl.id.index == nodes.size());
  if (!decl.anonymous &&
      !canonicalDeclarations.emplace(decl.qualifiedName, decl.id).second)
    return false;
  auto selectedCategory = category(decl);
  if (origin == SourceOrigin::Installation)
    if (auto *row = protocol::frontendDeclaration(decl.qualifiedName)) {
      if (row->rule == protocol::FrontendSignature::RandomConstructor)
        selectedCategory = ResolutionCategory::ServiceConstructor;
      if (row->prelude)
        prelude.emplace(
            row->name,
            NamespaceBinding{decl.id, decl.span, true, decl.module, {}});
    }
  nodes.push_back(
      {decl.parent, decl.module, decl.kind, selectedCategory, origin});
  namespaces.emplace_back();
  if (decl.kind == Declaration::Kind::Module) {
    moduleMembers.emplace(decl.id.index, std::vector<DeclarationId>{});
    if (!decl.parent)
      roots.emplace(decl.qualifiedName, decl.id);
  }
  if (decl.parent) {
    moduleMembers[decl.parent->index].push_back(decl.id);
    if (!decl.anonymous)
      namespaces[decl.parent->index].emplace(
          decl.name,
          NamespaceBinding{decl.id, decl.span, decl.isPublic, {}, {}});
  }
  return true;
}
DeclarationIndex::Namespace &
DeclarationIndex::formingNamespace(DeclarationId id) {
  assert(!frozen);
  return namespaces.at(id.index);
}
const DeclarationIndex::Namespace &
DeclarationIndex::bindings(DeclarationId id) const {
  return namespaces.at(id.index);
}
void DeclarationIndex::finish(ArrayRef<Declaration> declarations,
                              ArrayRef<SourceBuffer> sources) {
  assert(!frozen);
  for (const auto &decl : declarations) {
    if (decl.kind == Declaration::Kind::Record ||
        decl.kind == Declaration::Kind::Variant ||
        decl.kind == Declaration::Kind::Associated)
      nominalHomes.emplace(decl.qualifiedName, decl.module);
    if (sources[decl.span.source.index].origin != SourceOrigin::Installation)
      continue;
    if (auto *row = protocol::frontendDeclaration(decl.qualifiedName)) {
      associations.emplace(decl.id.index, row);
    }
  }
  for (const auto &row : protocol::frontendHomes()) {
    auto module = canonical(row.module);
    if (!module || nodes[module->index].kind != Declaration::Kind::Module)
      continue;
    constructorHomes.emplace(row.constructor, *module);
    for (const auto &member : row.members) {
      auto target = canonical(member);
      if (!target)
        continue;
      const auto &decl = declarations[target->index];
      auto at = namespaces[module->index].find(decl.name);
      if (at != namespaces[module->index].end() &&
          at->second.target.index == target->index && at->second.isPublic &&
          decl.isPublic &&
          !llvm::any_of(moduleMembers[module->index],
                        [&](auto id) { return id.index == target->index; }))
        moduleMembers[module->index].push_back(*target);
    }
  }
  frozen = true;
}
std::optional<DeclarationId>
DeclarationIndex::context(const AccessContext &access) const {
  if (auto *source = std::get_if<SourceAccess>(&access))
    return source->context;
  if (auto *import = std::get_if<ImportBindingAccess>(&access))
    return import->context;
  return {};
}
bool DeclarationIndex::within(DeclarationId child, DeclarationId parent) const {
  for (auto scope = std::optional(child); scope && scope->index < nodes.size();
       scope = nodes[scope->index].parent)
    if (scope->index == parent.index)
      return true;
  return false;
}
LookupResult DeclarationIndex::member(const AccessContext &access,
                                      DeclarationId owner, StringRef name,
                                      const LookupTraversal &traversal) const {
  if (!charge(traversal))
    return LookupFailure{LookupFailureKind::Limit, owner, name.str()};
  if (owner.index >= nodes.size())
    return LookupFailure{LookupFailureKind::NotFound, owner, name.str()};
  if (traversal.load && nodes[owner.index].kind == Declaration::Kind::Module)
    if (auto failure = traversal.load(owner, name))
      return *failure;
  auto at = namespaces[owner.index].find(name.str());
  if (at == namespaces[owner.index].end())
    return LookupFailure{LookupFailureKind::NotFound, owner, name.str()};
  const auto &binding = at->second;
  if (auto *import = std::get_if<ImportBindingAccess>(&access);
      import && owner.index == import->context.index &&
      binding.import == import->import)
    return LookupFailure{LookupFailureKind::NotFound, {}, name.str()};
  if (auto *source = std::get_if<SourceAccess>(&access);
      source && !binding.isPublic &&
      (source->context.index >= nodes.size() ||
       !within(nodes[source->context.index].module, nodes[owner.index].module)))
    return LookupFailure{LookupFailureKind::Inaccessible, binding.target,
                         name.str(), binding.span};
  return ResolvedReference{
      binding.provider.value_or(nodes[binding.target.index].module),
      binding.target,
      nodes[binding.target.index].category,
      {{owner, name.str(), binding.import}},
      {}};
}
LookupResult
DeclarationIndex::scopeBinding(const AccessContext &access, StringRef name,
                               const LookupTraversal &traversal) const {
  auto owner = context(access);
  if (!owner || owner->index >= nodes.size())
    return LookupFailure{LookupFailureKind::NotFound, {}, name.str()};
  auto scope = (nodes[owner->index].kind == Declaration::Kind::Module ||
                nodes[owner->index].kind == Declaration::Kind::Interface)
                   ? owner
                   : nodes[owner->index].parent;
  for (; scope; scope = nodes[scope->index].parent) {
    auto result = member(access, *scope, name, traversal);
    if (auto *failure = std::get_if<LookupFailure>(&result);
        failure && failure->kind == LookupFailureKind::NotFound)
      continue;
    return result;
  }
  return LookupFailure{LookupFailureKind::NotFound, {}, name.str()};
}
LookupResult DeclarationIndex::lookup(const AccessContext &access,
                                      StringRef name,
                                      const LookupTraversal &traversal) const {
  if (!charge(traversal))
    return LookupFailure{LookupFailureKind::Limit, {}, name.str()};
  bool absolute = name.consume_front("::");
  auto [head, tail] = name.split("::");
  std::optional<ResolvedReference> selected;
  auto select = [&](LookupResult result) -> std::optional<LookupFailure> {
    if (auto *ref = std::get_if<ResolvedReference>(&result))
      selected = std::move(*ref);
    else if (auto failure = std::get<LookupFailure>(std::move(result));
             failure.kind != LookupFailureKind::NotFound)
      return failure;
    return {};
  };
  auto selectRoot = [&]() -> std::optional<LookupFailure> {
    auto prefix = name;
    while (!prefix.empty()) {
      if (!charge(traversal))
        return LookupFailure{LookupFailureKind::Limit, {}, prefix.str()};
      auto at = roots.find(prefix.str());
      if (at != roots.end()) {
        auto root = at->second;
        selected =
            ResolvedReference{root, root, nodes[root.index].category, {}, {}};
        tail = name.size() == prefix.size()
                   ? StringRef{}
                   : name.drop_front(prefix.size() + 2);
        break;
      }
      prefix = prefix.contains("::") ? prefix.rsplit("::").first : StringRef{};
    }
    return {};
  };
  // A qualified external name first selects its exact captured/installed
  // root. Only an unqualified head (or a unique project alias) uses the
  // cross-module short-name inventory.
  if (!absolute && name.contains("::") &&
      std::holds_alternative<ExternalSelectionAccess>(access))
    if (auto failure = selectRoot())
      return *failure;
  if (!absolute && !selected) {
    if (auto owner = context(access); owner && owner->index < nodes.size()) {
      if (auto failure = select(scopeBinding(access, head, traversal)))
        return *failure;
    } else if (std::holds_alternative<ExternalSelectionAccess>(access)) {
      std::map<uint32_t, ResolvedReference> candidates;
      for (const auto &[path, root] : roots) {
        if (!charge(traversal))
          return LookupFailure{LookupFailureKind::Limit, {}, head.str()};
        if (nodes[root.index].origin != SourceOrigin::Captured)
          continue;
        if (path == head)
          candidates.emplace(
              root.index, ResolvedReference{
                              root, root, nodes[root.index].category, {}, {}});
      }
      for (unsigned i = 0; i < nodes.size(); ++i) {
        if (!charge(traversal))
          return LookupFailure{LookupFailureKind::Limit, {}, head.str()};
        if (nodes[i].kind != Declaration::Kind::Module ||
            nodes[i].origin != SourceOrigin::Captured)
          continue;
        auto result = member(access, DeclarationId{i}, head, traversal);
        if (auto *ref = std::get_if<ResolvedReference>(&result))
          candidates.emplace(ref->target.index, *ref);
        else if (auto failure = std::get<LookupFailure>(result);
                 failure.kind != LookupFailureKind::NotFound)
          return failure;
      }
      if (candidates.size() > 1)
        return LookupFailure{LookupFailureKind::Ambiguous, {}, head.str()};
      if (!candidates.empty())
        selected = candidates.begin()->second;
    }
  }
  if (!selected)
    if (auto failure = selectRoot())
      return *failure;
  if (!selected && !absolute) {
    auto at = prelude.find(head.str());
    if (at != prelude.end()) {
      const auto &binding = at->second;
      selected = ResolvedReference{*binding.provider,
                                   binding.target,
                                   nodes[binding.target.index].category,
                                   {{*binding.provider, head.str(), {}}},
                                   {}};
    }
  }
  if (!selected)
    return LookupFailure{LookupFailureKind::NotFound, {}, head.str()};
  while (!tail.empty()) {
    auto next = tail.split("::");
    auto result = member(access, selected->target, next.first, traversal);
    if (auto *failure = std::get_if<LookupFailure>(&result)) {
      failure->selected = selected->target;
      return *failure; // A selected root is terminal, even for optional probes.
    }
    auto ref = std::get<ResolvedReference>(std::move(result));
    selected->target = ref.target;
    selected->category = ref.category;
    selected->path.insert(selected->path.end(), ref.path.begin(),
                          ref.path.end());
    tail = next.second;
  }
  return *selected;
}
LookupResult
DeclarationIndex::homeMember(const AccessContext &access, DeclarationId home,
                             StringRef name,
                             const LookupTraversal &traversal) const {
  auto result = member(access, home, name, traversal);
  if (auto *ref = std::get_if<ResolvedReference>(&result)) {
    if (!llvm::any_of(members(home),
                      [&](auto id) { return id.index == ref->target.index; }))
      return LookupFailure{LookupFailureKind::WrongCategory, ref->target,
                           name.str()};
    ref->provider = home;
  }
  return result;
}
std::map<std::string, ResolvedReference>
DeclarationIndex::accessible(SourceAccess access) const {
  auto owner = access.context;
  std::map<std::string, ResolvedReference> result;
  std::set<std::string> seen;
  if (owner.index >= nodes.size())
    return result;
  auto start = (nodes[owner.index].kind == Declaration::Kind::Module ||
                nodes[owner.index].kind == Declaration::Kind::Interface)
                   ? std::optional(owner)
                   : nodes[owner.index].parent;
  for (auto scope = start; scope; scope = nodes[scope->index].parent)
    for (const auto &[name, binding] : bindings(*scope)) {
      if (!seen.insert(name).second)
        continue;
      auto selected = member(SourceAccess{owner}, *scope, name);
      if (auto *ref = std::get_if<ResolvedReference>(&selected))
        result.emplace(name, *ref);
    }
  for (const auto &[name, binding] : prelude)
    if (seen.insert(name).second)
      result.emplace(name,
                     ResolvedReference{*binding.provider,
                                       binding.target,
                                       nodes[binding.target.index].category,
                                       {{*binding.provider, name, {}}},
                                       {}});
  return result;
}
uint64_t DeclarationIndex::bindingCount() const {
  uint64_t count = prelude.size();
  for (const auto &scope : namespaces)
    count += scope.size();
  return count;
}
const protocol::FrontendDeclaration *
DeclarationIndex::association(DeclarationId id) const {
  auto at = associations.find(id.index);
  return at == associations.end() ? nullptr : at->second;
}
const protocol::FrontendDeclaration *
DeclarationIndex::ruleAssociation(DeclarationId id) const {
  const auto *row = association(id);
  return row && row->rule ? row : nullptr;
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
  // Builtin.domain is the checked catalog constructor identity; a logical
  // handle's head is its frontend constructor row. Domain names of field/group
  // types and printed aliases are never home lookup keys.
  StringRef head = type.kind == Type::Kind::Builtin ? StringRef(type.domain)
                   : isOracleHandle(type)           ? oracleConstructor(type)
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
