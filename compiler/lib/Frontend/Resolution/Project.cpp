#include "Project.h"
#include "../Syntax/Captures.h"
#include "Declarations.h"
#include "Installed.h"
#include "Names.h"
#include "OperatorRecovery.h"
#include "Vocabulary.h"
#include "zkc/Source/Relations.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"

using namespace llvm;
namespace zkc::frontend::resolution {
bool Context::operationAvailable(const source::Node &node,
                                 StringRef contract) const {
  if (!node.location)
    return false;
  const auto found = installedModules.find(node.location->file);
  if (found == installedModules.end())
    return false;
  return llvm::any_of(protocol::sourceOperationExports(), [&](const auto &op) {
    return op.contract == contract && found->second.count(op.module);
  });
}
bool Context::sourceOperatorAvailable(const source::Node &node,
                                      StringRef symbol) const {
  if (!node.location)
    return false;
  auto found = sourceOperators.find(node.location->file);
  return found != sourceOperators.end() && found->second.count(symbol.str());
}
const Declaration *Context::lookup(StringRef symbol) const {
  auto it = symbols.find(symbol.str());
  return it == symbols.end() ? nullptr : &declarations[it->second];
}
const Declaration *Context::lookup(const library::QualifiedDecl &id) const {
  auto q = id;
  for (;;) {
    auto it = nominalDeclarations.find(library::identity(q));
    if (it != nominalDeclarations.end())
      return &declarations[it->second];
    if (q.module.empty())
      return nullptr;
    q.name = q.module.back();
    q.module.pop_back();
  }
}
const Declaration *Context::enclosing(const source::Node &n) const {
  if (!n.location || n.location->file >= intervals.size())
    return nullptr;
  const auto &file = intervals[n.location->file];
  auto it = std::upper_bound(file.begin(), file.end(), n.location->offset,
                             [&](size_t offset, uint32_t i) {
                               return offset < declarations[i].location->offset;
                             });
  if (it == file.begin())
    return nullptr;
  const auto &d = declarations[*--it];
  return n.location->offset - d.location->offset < d.location->length ? &d
                                                                      : nullptr;
}
library::QualifiedDecl Context::qualify(StringRef name,
                                        ArrayRef<std::string> module) const {
  if (module.empty()) {
    if (auto *d = lookup(name))
      return d->identity;
  } else if (auto *d = lookup(module.front())) {
    auto q = d->identity;
    q.module.push_back(q.name);
    q.module.insert(q.module.end(), module.begin() + 1, module.end());
    q.name = name.str();
    return q;
  }
  return {
      {}, std::vector<std::string>(module.begin(), module.end()), name.str()};
}
std::string Context::origin(const library::QualifiedDecl &id) const {
  if (const auto *d = lookup(id)) {
    auto result = d->origin;
    if (library::identity(d->identity) != library::identity(id)) {
      for (size_t i = d->identity.module.size() + 1; i < id.module.size(); ++i)
        result += "." + id.module[i];
      result += "." + id.name;
    }
    return result;
  }
  auto result = llvm::join(id.module, ".");
  return result.empty() ? id.name : result + "." + id.name;
}
namespace {
std::string digest(StringRef value) {
  auto bytes = SHA256::hash(arrayRefFromStringRef(value));
  return toHex(bytes, true);
}
// Prefixes of the symbols the compiler generates into the namespace that
// authored declarations share: imported and module declarations, linked library
// functions and their client entries, and library operation bindings. Their
// suffixes are digests and counters, so an authored name with one of these
// prefixes would collide only when one happened to match, and whether a project
// is accepted would depend on content unrelated to that name.
std::optional<StringRef> reservedPrefix(StringRef name) {
  for (StringRef prefix :
       {"src_", "lib_", "client_", "__library_operation_", "__installed_"})
    if (name.starts_with(prefix))
      return prefix;
  return std::nullopt;
}
// A public generated relation helper is spelled `<view>_<member>` with one of
// these members; this is the view's spelling when `name` is one. Generated
// operation bindings and other suffixes are not helpers.
std::optional<StringRef> viewHelperOwner(StringRef name) {
  auto separator = name.rfind('_');
  if (separator == StringRef::npos)
    return std::nullopt;
  auto member = name.drop_front(separator + 1);
  bool helper = member == "Assemble" || member == "Products" ||
                member == "Residuals" || member == "Evaluate" ||
                member == "Contract";
  for (StringRef stem : {"BindingPoint", "CheckBinding"}) {
    auto tail = member;
    helper |= tail.consume_front(stem) && !tail.empty() &&
              llvm::all_of(tail, [](char c) { return llvm::isDigit(c); });
  }
  if (!helper)
    return std::nullopt;
  return name.take_front(separator);
}
std::string ownerIdentity(const library::LibraryId &id) {
  return library::identity(library::QualifiedDecl{id, {}, "library"});
}
library::LibraryId identity(const syntax::LibraryIdentity &i) {
  return {i.nameSpace, i.name, i.version, i.resolution};
}
// Snapshot-scoped anonymous identity. Exact framed captured bytes, not file
// paths or allocator addresses, determine the scope; source ordering does not.
std::string anonymousScope(const ProjectInput &input) {
  auto frame = [](StringRef s) {
    return std::to_string(s.size()) + ":" + s.str();
  };
  std::vector<std::string> owners, fileKeys;
  for (const auto &library : input.libraries()) {
    std::vector<std::string> units;
    for (const auto &unit : library.sources) {
      std::string key;
      for (const auto &part : unit.module)
        key += frame(part);
      key = frame(key) + frame(unit.input.text());
      units.push_back(key);
      fileKeys.push_back(key);
    }
    llvm::sort(units);
    std::string owner;
    for (const auto &unit : units)
      owner += frame(unit);
    owners.push_back(owner);
  }
  if (owners.size() > 1)
    llvm::sort(owners.begin() + 1, owners.end());
  SHA256 hash;
  hash.update("zkc.anonymous-project/1");
  auto add = [&](StringRef bytes) {
    hash.update(std::to_string(bytes.size()) + ":");
    hash.update(bytes);
  };
  for (const auto &owner : owners)
    add(owner);
  std::vector<const ProjectAsset *> assets;
  for (const auto &asset : input.assets())
    assets.push_back(&asset);
  llvm::sort(assets, [&](const auto *a, const auto *b) {
    return std::tie(fileKeys.at(a->file), a->path, a->bytes) <
           std::tie(fileKeys.at(b->file), b->path, b->bytes);
  });
  for (const auto *asset : assets) {
    add(fileKeys.at(asset->file));
    add(asset->path);
    add(asset->bytes);
  }
  return toHex(hash.final(), true);
}
// A lexical binding. A declaration binding can also select a generated view
// helper (`helper` extends its identifier) or members below the declaration.
struct Binding {
  enum class Kind { Declaration, Module, Use } kind;
  uint32_t index;
  bool exported;
  std::string helper = {};
  source::Names members = {};
  bool exact() const { return helper.empty() && members.empty(); }
};
struct Module {
  uint32_t owner, file;
  source::Names path;
  syntax::Module syntax;
  std::map<std::string, Binding> names;
};
class Resolver {
  std::shared_ptr<Context> context;
  std::vector<Module> modules;
  std::vector<Diagnostic> diagnostics;
  std::optional<syntax::Content> standalone;
  std::map<std::pair<uint32_t, source::Names>, uint32_t> paths;
  std::set<std::pair<uint32_t, uint32_t>> resolving;
  std::map<std::pair<uint32_t, uint32_t>, Binding> aliases;
  std::map<uint32_t, std::set<uint32_t>> signatureReferences;
  std::map<uint32_t, std::vector<std::string>> componentMembers;
  size_t work = 0;
  size_t assetCount = 0, assetBytes = 0;
  bool syntaxPartial = false;
  std::optional<uint32_t> installedRoot;
  static constexpr size_t maxWork = 262144;

  std::optional<uint32_t> enclosing(const source::Node &n) const {
    if (const auto *d = context->enclosing(n))
      return uint32_t(d - context->declarations.data());
    return {};
  }
  bool spend(const source::Node &node) {
    if (work >= maxWork) {
      if (work++ == maxWork)
        fail(node, "source-resolution-limit", "name resolution work exhausted");
      return false;
    }
    ++work;
    return true;
  }
  void fail(const source::Node &n, StringRef code, const Twine &message) {
    if (auto owner = enclosing(n))
      context->unavailable.insert(context->declarations[*owner].symbol);
    if (diagnostics.size() < 256)
      diagnostics.push_back({code.str(), message.str(), n.location});
    else
      diagnostics.back() = {"source-diagnostic-limit",
                            "project diagnostic budget exhausted", n.location};
  }
  bool inside(uint32_t request, uint32_t target) const {
    const auto &a = modules[request];
    const auto &b = modules[target];
    return a.owner == b.owner && a.path.size() >= b.path.size() &&
           std::equal(b.path.begin(), b.path.end(), a.path.begin());
  }
  void insert(uint32_t module, StringRef name, Binding value,
              const source::Node &node) {
    if (name == "zkc") {
      fail(node, "source-name-reserved",
           "zkc names the installed library namespace");
      // Keep the rejected declaration's locator for later diagnostics and
      // collection. Binding/component bookkeeping still visits this syntax.
      if (value.kind == Binding::Kind::Declaration)
        context->unavailable.insert(context->declarations[value.index].symbol);
    }
    if (!modules[module].names.emplace(name.str(), value).second)
      fail(node, "source-name-duplicate", "duplicate name '" + name + "'");
  }
  std::optional<Binding> use(uint32_t module, uint32_t index) {
    auto key = std::make_pair(module, index);
    if (auto i = aliases.find(key); i != aliases.end())
      return i->second;
    auto &u = modules[module].syntax.uses[index];
    if (resolving.size() >= 64) {
      fail(u, "source-resolution-limit", "import expansion exceeds 64 levels");
      return {};
    }
    if (!resolving.insert(key).second) {
      fail(u, "source-import-cycle", "cyclic import or reexport");
      return {};
    }
    auto result = path(module, u.path, module, u);
    resolving.erase(key);
    if (!result)
      return {};
    if (u.exported && !result->exported) {
      fail(u, "source-private-reexport",
           "cannot reexport a private declaration");
      return {};
    }
    aliases.emplace(key, *result);
    return result;
  }
  std::optional<Binding> lookup(uint32_t module, StringRef name,
                                uint32_t request, const source::Node &node,
                                bool required = true) {
    if (!spend(node))
      return {};
    auto found = modules[module].names.find(name.str());
    if (found == modules[module].names.end()) {
      // Generated operations are members of a resolved relation-view owner.
      // Importing/reexporting that view grants the same public helper surface;
      // an unrelated same-spelled view or generated symbol grants nothing.
      // Probe lexical view prefixes, never all declarations in the module.
      // Only public generated helper categories are source-callable.
      if (auto prefix = viewHelperOwner(name)) {
        auto entry = modules[module].names.find(prefix->str());
        if (entry != modules[module].names.end()) {
          auto owner = entry->second.kind == Binding::Kind::Use
                           ? use(module, entry->second.index)
                           : std::optional<Binding>(entry->second);
          if (owner && owner->kind == Binding::Kind::Declaration &&
              context->declarations[owner->index].kind ==
                  Declaration::Kind::View) {
            if (!entry->second.exported && !inside(request, module)) {
              fail(node, "source-name-private",
                   "private relation view '" + *prefix + "'");
              return {};
            }
            owner->helper += name.drop_front(prefix->size()).str();
            return owner;
          }
        }
      }
      if (required)
        fail(node, "source-name-unresolved", "unknown name '" + name + "'");
      return {};
    }
    auto b = found->second;
    if (!b.exported && !inside(request, module)) {
      fail(node, "source-name-private", "private name '" + name + "'");
      return {};
    }
    if (b.kind == Binding::Kind::Use)
      return use(module, b.index);
    return b;
  }
  // A declaration path another declaration's members are resolved through.
  struct Target {
    uint32_t module;
    source::Names path;
    ReferenceKind kind = ReferenceKind::Declaration;
  };
  struct Surface {
    std::set<std::string> types, calls;
    std::map<std::string, std::string> statics;
    std::map<std::string, Target> dependencies;
    std::optional<Target> base, viewRelation;
    bool bindingHelpers = false;
  };
  std::map<uint32_t, Surface> surfaces;
  std::map<uint32_t, uint32_t> relationPublicCounts;
  struct Candidate {
    Binding binding;
    bool visible;
  };

  // Snapshot member names before qualification mutates the syntax. A selected
  // component exposes its target's surface; a configured protocol exposes its
  // base's dependency paths. Neither an ordinary function nor a record is a
  // namespace for arbitrary suffixes.
  void memberSurfaces() {
    for (uint32_t module = 0; module < modules.size(); ++module) {
      const auto &m = modules[module];
      auto surface = [&](StringRef name) -> Surface & {
        return surfaces[m.names.at(name.str()).index];
      };
      auto members = [&](const auto &d) {
        auto &out = surface(d.name);
        for (const auto &t : d.types)
          out.types.insert(t.name);
        for (const auto &v : d.statics) {
          auto sort = v.domain;
          if (!sort.empty())
            sort.front() = llvm::toUpper(sort.front());
          out.statics.emplace(v.name, std::move(sort));
        }
        for (const auto &f : d.functions)
          out.calls.insert(f.name);
      };
      for (const auto &d : m.syntax.relations)
        if (auto r =
                std::get_if<std::shared_ptr<const relation::R1CS>>(&d.value))
          relationPublicCounts.emplace(m.names.at(d.name).index,
                                       (*r)->publicCount());
      for (const auto &d : m.syntax.relationViews) {
        auto &out = surface(d.name);
        if (d.kind == "rank_one")
          out.calls = {"Assemble", "Products", "Residuals"};
        else if (d.kind == "multilinear") {
          out.calls = {"Assemble", "Products", "Contract", "Evaluate"};
          out.bindingHelpers = true;
          out.viewRelation = Target{module, d.relation.path.segments};
        } else if (d.kind == "arithmetic")
          out.calls = {"Evaluate"};
      }
      for (const auto &d : m.syntax.libraryComponents)
        members(d);
      // An exact quoted selection is installed data with no member surface.
      for (const auto &d : m.syntax.librarySelections)
        if (d.target.root.kind == syntax::Atom::Kind::Name) {
          source::Names target{d.target.root.value};
          llvm::append_range(target, d.target.members);
          surface(d.name).base =
              Target{module, std::move(target), ReferenceKind::Static};
        }
      for (const auto &d : m.syntax.enums)
        for (const auto &v : d.alternatives)
          surface(d.name).calls.insert(v.name);
      for (const auto &d : m.syntax.protocols)
        for (const auto &v : d.dependencies)
          surface(d.name).dependencies.emplace(
              v.name, Target{module, v.protocol.path.segments});
      for (const auto &d : m.syntax.instances)
        for (const auto &v : d.dependencies)
          surface(d.name).dependencies.emplace(
              v.first, Target{module, v.second.path.segments});
      for (const auto &d : m.syntax.configurations)
        surface(d.name).base = Target{module, d.base.path.segments};
    }
  }

  // Read resolved imports without emitting diagnostics or granting visibility
  // through a private alias. Existence and visibility stay separate so a
  // private target receives an access diagnostic, never authority.
  std::optional<Candidate> candidateName(uint32_t module, StringRef name,
                                         uint32_t request) const {
    auto entry = modules[module].names.find(name.str());
    std::string helper;
    if (entry == modules[module].names.end()) {
      auto prefix = viewHelperOwner(name);
      if (!prefix)
        return {};
      entry = modules[module].names.find(prefix->str());
      if (entry == modules[module].names.end())
        return {};
      helper = name.drop_front(prefix->size()).str();
    }
    auto b = entry->second;
    bool visible = b.exported || inside(request, module);
    if (b.kind == Binding::Kind::Use) {
      auto alias = aliases.find({module, b.index});
      if (alias == aliases.end())
        return {};
      b = alias->second;
    }
    if (!helper.empty()) {
      if (b.kind != Binding::Kind::Declaration || !b.exact() ||
          context->declarations[b.index].kind != Declaration::Kind::View)
        return {};
      b.helper = helper;
    }
    return Candidate{b, visible};
  }

  bool authorizes(Binding &b, ReferenceKind kind, const source::Node &node,
                  unsigned depth = 0) {
    if (depth > 64) {
      fail(node, "source-resolution-limit",
           "member resolution exceeds 64 levels");
      return false;
    }
    if (b.kind != Binding::Kind::Declaration)
      return false;
    using K = Declaration::Kind;
    const auto k = context->declarations[b.index].kind;
    if (b.exact()) {
      switch (kind) {
      case ReferenceKind::Value:
        return k == K::Constant;
      case ReferenceKind::Constructor:
        return k == K::Record;
      case ReferenceKind::Call:
        return k == K::Function || k == K::Configuration || k == K::Link ||
               k == K::Binding || k == K::Operation;
      case ReferenceKind::Type:
        return k == K::Record || k == K::Enum || k == K::Interface ||
               k == K::Component || k == K::Selection || k == K::LogicalType;
      case ReferenceKind::Static:
        return k == K::Constant || k == K::Association || k == K::Relation ||
               k == K::Interface || k == K::Component || k == K::Selection ||
               k == K::LogicalType;
      case ReferenceKind::Predicate:
        return k == K::Interface || k == K::Bundle || k == K::Capability;
      case ReferenceKind::Declaration:
        return true;
      }
    }
    auto found = surfaces.find(b.index);
    if (found == surfaces.end())
      return false;
    const auto &surface = found->second;
    if (!b.helper.empty()) {
      // A generated view helper is callable, never a namespace.
      if (k != K::View || !b.members.empty() || kind != ReferenceKind::Call)
        return false;
      auto helper = StringRef(b.helper).drop_front();
      if (surface.calls.count(helper.str()))
        return true;
      if (!surface.bindingHelpers)
        return false;
      if (!helper.consume_front("BindingPoint") &&
          !helper.consume_front("CheckBinding"))
        return false;
      uint32_t coordinate;
      if (helper.empty() || helper.getAsInteger(10, coordinate) ||
          helper != std::to_string(coordinate))
        return false;
      const auto &target = *surface.viewRelation;
      auto relations = candidates(target.module, target.path, target.module,
                                  ReferenceKind::Declaration, node, depth + 1);
      if (relations.size() != 1 || !relations.front().visible ||
          !relations.front().binding.exact())
        return false;
      auto count = relationPublicCounts.find(relations.front().binding.index);
      return count != relationPublicCounts.end() && coordinate <= count->second;
    }
    const auto &head = b.members.front();
    const auto tail = ArrayRef(b.members).drop_front();
    if (surface.base) {
      // A selected component or configured protocol exposes its target's
      // members under its own name.
      const auto &base = *surface.base;
      auto targets = candidates(base.module, base.path, base.module, base.kind,
                                node, depth + 1);
      if (targets.size() != 1 || !targets.front().visible)
        return false;
      auto target = targets.front().binding;
      llvm::append_range(target.members, b.members);
      return authorizes(target, kind, node, depth + 1);
    }
    if (kind == ReferenceKind::Call)
      return tail.empty() && surface.calls.count(head);
    if (tail.empty() &&
        ((kind == ReferenceKind::Type && surface.types.count(head)) ||
         (kind == ReferenceKind::Static && surface.statics.count(head))))
      return true;
    // Domain members carry a sort. Check every associated-domain projection
    // against the installed vocabulary before recognizing its final type.
    auto domain = surface.statics.find(head);
    if (domain != surface.statics.end() && !tail.empty()) {
      StringRef sort = domain->second;
      for (size_t i = 0; i < tail.size() && !sort.empty(); ++i) {
        if (!spend(node))
          return false;
        if (i + 1 == tail.size() && kind == ReferenceKind::Type)
          return !associatedTypeConstructor(sort, tail[i]).empty();
        sort = protocol::associatedMemberSort(sort, tail[i]);
      }
      return kind == ReferenceKind::Static && !sort.empty();
    }
    if (kind != ReferenceKind::Declaration)
      return false;
    auto dependency = surface.dependencies.find(head);
    if (dependency == surface.dependencies.end())
      return false;
    const auto &target = dependency->second;
    auto targets = candidates(target.module, target.path, target.module, kind,
                              node, depth + 1);
    if (targets.size() != 1 || !targets.front().visible)
      return false;
    if (tail.empty())
      return true;
    auto nested = targets.front().binding;
    llvm::append_range(nested.members, tail);
    return authorizes(nested, kind, node, depth + 1);
  }

  // Invalid members never compete with complete candidates. When no complete
  // reading exists, a unique enum/protocol owner can still provide the precise
  // semantic leaf diagnostic.
  bool leafOwner(const Binding &b, ReferenceKind kind) const {
    if (b.kind != Binding::Kind::Declaration || b.members.empty())
      return false;
    using K = Declaration::Kind;
    const auto k = context->declarations[b.index].kind;
    return (kind == ReferenceKind::Call && k == K::Enum &&
            b.members.size() == 1) ||
           (kind == ReferenceKind::Declaration &&
            (k == K::Protocol || k == K::Configuration || k == K::Instance));
  }

  // Resolve a path segment by segment. The first segment is a lexical name
  // or a scope root; each module segment selects the next; a declaration
  // keeps the remaining segments as members for category authorization.
  std::vector<Candidate> candidates(uint32_t module, ArrayRef<std::string> path,
                                    uint32_t request, ReferenceKind kind,
                                    const source::Node &node,
                                    unsigned depth = 0, bool root = true,
                                    bool diagnosticOnly = false) {
    std::vector<Candidate> out;
    if (depth > 64) {
      fail(node, "source-resolution-limit",
           "candidate resolution exceeds 64 levels");
      return out;
    }
    // reference() charged the root; each traversed namespace is charged once.
    if (path.empty() || (depth != 0 && !spend(node)))
      return out;
    const auto &head = path.front();
    auto candidate = candidateName(module, head, request);
    bool scopeRoot = head == "crate" || head == "self" || head == "super";
    if (root && (!candidate || scopeRoot)) {
      if (scopeRoot)
        candidate.reset();
      std::optional<uint32_t> target;
      const auto &owner = context->owners[modules[module].owner];
      if (head == "crate")
        target = owner.root;
      else if (head == "self")
        target = module;
      else if (head == "zkc" && installedRoot)
        target = *installedRoot;
      else if (head == "super") {
        auto p = modules[module].path;
        if (!p.empty()) {
          p.pop_back();
          auto parent = paths.find({modules[module].owner, p});
          if (parent != paths.end())
            target = parent->second;
        }
      } else if (auto dep = owner.dependencies.find(head);
                 dep != owner.dependencies.end())
        target = context->owners[dep->second].root;
      if (target)
        candidate =
            Candidate{Binding{Binding::Kind::Module, *target, true}, true};
    }
    if (!candidate)
      return out;
    auto &b = candidate->binding;
    if (b.kind == Binding::Kind::Declaration) {
      llvm::append_range(b.members, path.drop_front());
      if (diagnosticOnly ? leafOwner(b, kind)
                         : authorizes(b, kind, node, depth))
        out.push_back(std::move(*candidate));
    } else if (b.kind == Binding::Kind::Module && path.size() > 1) {
      for (auto c : candidates(b.index, path.drop_front(), request, kind, node,
                               depth + 1, false, diagnosticOnly)) {
        c.visible &= candidate->visible;
        out.push_back(std::move(c));
      }
    }
    return out;
  }
  // A module is exported when its parent declares it public; a library root
  // is its library's public surface. `self` and `super` name a module with
  // that visibility, so re-exporting one cannot widen it.
  bool exportedModule(uint32_t module) {
    auto p = modules[module].path;
    if (p.empty())
      return true;
    auto name = p.back();
    p.pop_back();
    auto parent = paths.find({modules[module].owner, p});
    return parent != paths.end() &&
           llvm::is_contained(modules[parent->second].syntax.exports, name);
  }
  std::optional<Binding> path(uint32_t module, ArrayRef<std::string> parts,
                              uint32_t request, const source::Node &node) {
    if (parts.empty())
      return {};
    std::optional<Binding> b;
    if (parts.front() == "crate")
      b = Binding{Binding::Kind::Module,
                  context->owners[modules[module].owner].root, true};
    else if (parts.front() == "zkc" && installedRoot)
      b = Binding{Binding::Kind::Module, *installedRoot, true};
    else if (parts.front() == "self")
      b = Binding{Binding::Kind::Module, module, exportedModule(module)};
    else if (parts.front() == "super") {
      auto p = modules[module].path;
      if (p.empty()) {
        fail(node, "source-module-parent", "root module has no parent");
        return {};
      }
      p.pop_back();
      auto parent = paths.find({modules[module].owner, p});
      if (parent == paths.end()) {
        fail(node, "source-module-parent", "parent module is not captured");
        return {};
      }
      b = Binding{Binding::Kind::Module, parent->second,
                  exportedModule(parent->second)};
    } else if (modules[module].names.count(parts.front()))
      b = lookup(module, parts.front(), request, node);
    else {
      const auto &deps = context->owners[modules[module].owner].dependencies;
      auto dep = deps.find(parts.front());
      if (dep != deps.end())
        b = Binding{Binding::Kind::Module, context->owners[dep->second].root,
                    true};
      else
        b = lookup(module, parts.front(), request, node);
    }
    for (const auto &part : parts.drop_front()) {
      if (!b)
        return {};
      if (b->kind != Binding::Kind::Module) {
        fail(node, "source-import-path", "path traverses a declaration");
        return {};
      }
      b = lookup(b->index, part, request, node);
    }
    return b;
  }
  // Resolve authored path segments in one reference category. The result is
  // the target that syntax records; failures are diagnosed here.
  std::optional<Resolved> reference(uint32_t module, const syntax::Path &path,
                                    const source::Node &node,
                                    ReferenceKind kind, bool signature) {
    const auto origin = enclosing(node);
    const auto before = diagnostics.size();
    auto failure = scope_exit([&] {
      if (origin && diagnostics.size() > before)
        context->unavailable.insert(context->declarations[*origin].symbol);
    });
    if (!spend(node) || path.segments.empty())
      return std::nullopt;
    const auto &segments = path.segments;
    const auto &head = segments.front();
    const auto written = syntax::spelling(path);
    const auto &deps = context->owners[modules[module].owner].dependencies;
    const bool lexicalHead =
        modules[module].names.count(head) || deps.count(head) ||
        llvm::any_of(modules[context->owners[modules[module].owner].root]
                         .syntax.dependencies,
                     [&](const auto &d) { return d.name == head; }) ||
        head == "crate" || head == "self" || head == "super" || head == "zkc";
    // An installed predicate without a source export is named by the
    // segments of its dotted vocabulary key, e.g. Encodes::field, when no
    // lexical name owns the path's head.
    if (kind == ReferenceKind::Predicate && segments.size() > 1 &&
        !lexicalHead) {
      auto word = llvm::join(segments, ".");
      if (installedPredicate(word))
        return Resolved{nullptr, {syntax::Target::Kind::Vocabulary, word, {}}};
    }
    // Core type words and installed predicates are vocabulary, unless a
    // lexical declaration of the same category shadows them.
    if (segments.size() == 1 &&
        ((kind == ReferenceKind::Type && installedType(head)) ||
         (kind == ReferenceKind::Predicate && installedPredicate(head)))) {
      auto lexical = modules[module].names.find(head);
      bool sameNamespace = false;
      if (lexical != modules[module].names.end()) {
        auto target = lexical->second.kind == Binding::Kind::Use
                          ? use(module, lexical->second.index)
                          : std::optional<Binding>(lexical->second);
        if (target && target->kind == Binding::Kind::Declaration) {
          auto targetKind = context->declarations[target->index].kind;
          sameNamespace = kind == ReferenceKind::Type
                              ? targetKind == Declaration::Kind::Record ||
                                    targetKind == Declaration::Kind::Enum
                              : targetKind == Declaration::Kind::Interface ||
                                    targetKind == Declaration::Kind::Bundle ||
                                    targetKind == Declaration::Kind::Capability;
        }
      }
      if (!sameNamespace)
        return Resolved{nullptr, {syntax::Target::Kind::Vocabulary, head, {}}};
    }
    // Resolve the category-correct path before recording its symbol.
    // Existence alone does not grant access to a private declaration.
    auto choices = candidates(module, segments, module, kind, node);
    auto diagnosticChoices =
        choices.empty()
            ? candidates(module, segments, module, kind, node, 1, true, true)
            : std::vector<Candidate>{};
    std::optional<Binding> b;
    source::Names members;
    if (!choices.empty()) {
      if (!choices.front().visible) {
        fail(node, "source-name-private",
             "private name along path '" + written + "'");
        return std::nullopt;
      }
      b = choices.front().binding;
    } else if (diagnosticChoices.size() == 1) {
      if (!diagnosticChoices.front().visible) {
        fail(node, "source-name-private",
             "private name along path '" + written + "'");
        return std::nullopt;
      }
      b = diagnosticChoices.front().binding;
    } else {
      // No reading authorizes this category. Walk the namespace prefix once
      // more with diagnostics to report a missing, private or misused name.
      if (!lexicalHead) {
        // Generated relation helper names are lexically owned by their view.
        if (segments.size() == 1)
          b = lookup(module, head, module, node, false);
        if (!b) {
          fail(node, "source-name-unresolved",
               "name has no local, resolved declaration, or installed "
               "authority: '" +
                   written + "'");
          return std::nullopt;
        }
      } else {
        for (size_t count = 1; count <= segments.size(); ++count) {
          b = this->path(module, ArrayRef(segments).take_front(count), module,
                         node);
          if (!b)
            return std::nullopt;
          if (b->kind == Binding::Kind::Declaration) {
            members.assign(segments.begin() + count, segments.end());
            break;
          }
        }
      }
    }
    if (!b)
      return std::nullopt;
    if (b->kind != Binding::Kind::Declaration) {
      fail(node, "source-name-kind", "a module is not a value or type");
      return std::nullopt;
    }
    const auto &d = context->declarations[b->index];
    llvm::append_range(b->members, members);
    // Candidate discovery requires complete members. If none exists, retain a
    // recognized enum/protocol owner for the semantic leaf checker: it can
    // report the missing alternative or dependency precisely. This fallback
    // never turns an ordinary function into a member namespace.
    const bool authorized =
        !choices.empty() || leafOwner(*b, kind) || authorizes(*b, kind, node);
    if (!authorized) {
      fail(
          node, "source-name-kind",
          "resolved declaration does not authorize this reference category: '" +
              written + "'");
      return std::nullopt;
    }
    if (origin) {
      context->references.push_back({context->declarations[*origin].symbol,
                                     d.symbol, node.location, signature});
      if (signature)
        signatureReferences[*origin].insert(b->index);
    }
    if (d.kind == Declaration::Kind::LogicalType ||
        d.kind == Declaration::Kind::Operation ||
        d.kind == Declaration::Kind::Capability)
      context->installedModules[modules[module].file].insert(
          "zkc::" + llvm::join(d.identity.module, "::"));
    if (d.kind == Declaration::Kind::Operation)
      return Resolved{&d, syntax::Target::operation(d.contract)};
    if (d.kind == Declaration::Kind::Capability)
      return Resolved{&d, {syntax::Target::Kind::Vocabulary, d.contract, {}}};
    return Resolved{&d,
                    {syntax::Target::Kind::Declaration, d.symbol + b->helper,
                     std::move(b->members)}};
  }
  // A quoted atom is exact data. In a static or type position it must name
  // installed vocabulary; it never selects a source declaration.
  void exact(StringRef value, const source::Node &node, ReferenceKind kind) {
    const auto origin = enclosing(node);
    if (installedExact(value, kind))
      return;
    fail(node, "source-name-unresolved",
         "quoted identifier does not name installed vocabulary: '" + value +
             "'");
    if (origin)
      context->unavailable.insert(context->declarations[*origin].symbol);
  }
  void ownerOrder(uint32_t owner, std::vector<unsigned> &states) {
    if (states[owner] == 2)
      return;
    if (states[owner] == 1) {
      fail(modules[context->owners[owner].root].syntax, "source-library-cycle",
           "library dependencies must be acyclic");
      return;
    }
    states[owner] = 1;
    for (const auto &[alias, target] : context->owners[owner].dependencies)
      ownerOrder(target, states);
    states[owner] = 2;
    context->order.push_back(owner);
  }
  void installDeclarations() {
    // Installed modules are typed declarations, not synthesized source files.
    // They use the same path, alias, visibility and reference machinery as
    // captured libraries, with an owner that source cannot impersonate.
    const uint32_t owner = context->owners.size();
    const uint32_t root = modules.size();
    installedRoot = root;
    context->owners.push_back(
        {{"zkc", "installed-contracts", "1", "builtin"}, root, {}});
    modules.push_back({owner, UINT32_MAX, {}, {}, {}});
    std::map<std::string, uint32_t> installedModules{{"zkc", root}};
    auto module = [&](StringRef path) {
      uint32_t parent = root;
      std::string prefix = "zkc";
      SmallVector<StringRef> parts;
      path.split(parts, "::");
      source::Names names;
      for (auto part : ArrayRef(parts).drop_front()) {
        names.push_back(part.str());
        prefix += "::" + part.str();
        auto found = installedModules.find(prefix);
        if (found == installedModules.end()) {
          const uint32_t child = modules.size();
          modules.push_back({owner, UINT32_MAX, names, {}, {}});
          modules[parent].names.emplace(
              part.str(), Binding{Binding::Kind::Module, child, true});
          installedModules.emplace(prefix, child);
          parent = child;
        } else
          parent = found->second;
      }
      return parent;
    };
    auto add = [&](StringRef path, StringRef name, StringRef contract,
                   Declaration::Kind kind, std::string symbol) {
      const uint32_t target = module(path);
      uint32_t index;
      if (auto existing = context->symbols.find(symbol);
          existing != context->symbols.end()) {
        index = existing->second;
        const auto &d = context->declarations[index];
        if (d.kind != kind || d.contract != contract || d.owner != owner)
          report_fatal_error("conflicting installed source declarations");
      } else {
        index = context->declarations.size();
        library::QualifiedDecl id{context->owners[owner].identity,
                                  modules[target].path, name.str()};
        context->nominalDeclarations.emplace(library::identity(id), index);
        context->symbols.emplace(symbol, index);
        context->declarations.push_back({std::move(id),
                                         kind,
                                         owner,
                                         UINT32_MAX,
                                         true,
                                         std::move(symbol),
                                         path.str() + "::" + name.str(),
                                         {},
                                         contract.str()});
      }
      if (!modules[target]
               .names
               .emplace(name.str(),
                        Binding{Binding::Kind::Declaration, index, true})
               .second)
        report_fatal_error("duplicate installed source export");
    };
    for (const auto &type : protocol::sourceTypeExports())
      add(type.module, type.name, type.constructor,
          Declaration::Kind::LogicalType,
          installedTypeSymbol(type.constructor));
    for (const auto &operation : protocol::sourceOperationExports())
      add(operation.module, operation.name, operation.contract,
          Declaration::Kind::Operation,
          installedOperationSymbol(operation.contract));
    for (const auto &capability : protocol::sourceCapabilityExports())
      add(capability.module, capability.name, capability.predicate,
          Declaration::Kind::Capability,
          "__installed_capability_" + capability.predicate);
  }
  bool collect() {
    std::map<std::string, uint32_t> identities;
    uint32_t file = 0;
    for (auto [owner, library] : enumerate(context->input.libraries())) {
      Owner record;
      record.root = UINT32_MAX;
      for (const auto &source : library.sources) {
        auto parsed = syntax::parseRecoverable(source.input.text(),
                                               source.input.filename(), file);
        syntaxPartial |= !parsed.complete();
        for (const auto &d : parsed.diagnostics)
          fail(source::Node{d.location}, d.code, d.message);
        syntax::Module syntax;
        if (parsed.content) {
          auto *m = std::get_if<syntax::Module>(&*parsed.content);
          if (!m) {
            if (context->input.libraries().size() == 1 &&
                library.sources.size() == 1) {
              standalone = std::move(*parsed.content);
              return false;
            }
            fail({}, "source-project-kind",
                 "a source project requires modules");
            return false;
          }
          syntax = std::move(*m);
        }
        for (const auto &asset : syntax.imports) {
          if (++assetCount > relation::DependencyLimits::count) {
            fail(asset, "relation-dependency-limit",
                 "too many relation imports");
            break;
          }
          auto captured =
              llvm::find_if(context->input.assets(), [&](const auto &a) {
                return a.file == file && a.path == asset.path;
              });
          if (captured == context->input.assets().end()) {
            fail(asset, "relation-unresolved",
                 "relation asset is not captured");
            continue;
          }
          if (captured->bytes.size() >
              relation::DependencyLimits::bytes - assetBytes) {
            fail(asset, "relation-dependency-limit",
                 "relation imports exceed the project byte budget");
            break;
          }
          assetBytes += captured->bytes.size();
          auto decoded = relation::decodeAsset(asset.family, captured->bytes);
          if (!decoded) {
            handleAllErrors(decoded.takeError(), [&](const Refusal &e) {
              fail(asset, e.code, e.detail);
            });
            continue;
          }
          decoded->name = asset.name;
          decoded->location = asset.location;
          syntax.relations.push_back(std::move(*decoded));
        }
        syntax.imports.clear();
        uint32_t index = modules.size();
        if (!paths.emplace(std::make_pair(owner, source.module), index).second)
          fail(syntax, "project-module-duplicate",
               "duplicate logical module path");
        if (source.module.empty()) {
          record.root = index;
          if (syntax.libraryIdentities.size() == 1)
            record.identity = identity(syntax.libraryIdentities.front());
          else if (owner == 0 && syntax.libraryIdentities.empty())
            record.identity = {"zkc", "application", "anonymous",
                               anonymousScope(context->input)};
          else
            fail(syntax, "source-library-identity",
                 "importable libraries require one explicit identity");
        } else if (!syntax.libraryIdentities.empty() ||
                   !syntax.dependencies.empty())
          fail(syntax, "source-library-root",
               "library identity and dependencies belong to the root");
        modules.push_back(
            {uint32_t(owner), file++, source.module, std::move(syntax), {}});
      }
      if (record.root == UINT32_MAX) {
        fail({}, "project-module-root", "library has no root module");
        return false;
      }
      if (!modules[record.root].syntax.libraryIdentities.empty() &&
          record.identity.nameSpace == "zkc" &&
          (record.identity.name == "installed-contracts" ||
           record.identity.name == "application"))
        fail(modules[record.root].syntax, "source-library-reserved",
             "installed and anonymous application owners cannot be declared by "
             "source");
      auto key = ownerIdentity(record.identity);
      if (!identities.emplace(key, owner).second)
        fail(modules[record.root].syntax, "source-library-conflict",
             "an exact library identity has more than one captured definition");
      context->owners.push_back(std::move(record));
    }
    for (auto [owner, record] : enumerate(context->owners)) {
      auto &root = modules[record.root];
      for (const auto &dep : root.syntax.dependencies) {
        if (dep.name == "zkc")
          fail(dep, "source-name-reserved",
               "the zkc namespace belongs to installed source modules");
        auto it = identities.find(ownerIdentity(identity(dep.identity)));
        if (it == identities.end()) {
          fail(dep, "source-dependency-missing",
               "exact dependency identity is not captured");
          continue;
        }
        if (!record.dependencies.emplace(dep.name, it->second).second)
          fail(dep, "source-dependency-duplicate",
               "duplicate dependency alias");
      }
    }
    // Identity, origins and acceptance come from the application's dependency
    // closure. A captured library outside it would still take part in origin
    // qualification below and so change the constructed artifact; refuse it
    // rather than let the set of supplied files become an undeclared input.
    std::vector<bool> reached(context->owners.size());
    std::vector<uint32_t> pending{0};
    reached[0] = true;
    while (!pending.empty()) {
      auto owner = pending.back();
      pending.pop_back();
      for (const auto &[alias, target] : context->owners[owner].dependencies)
        if (!reached[target]) {
          reached[target] = true;
          pending.push_back(target);
        }
    }
    for (auto [owner, record] : enumerate(context->owners))
      if (!reached[owner])
        fail(modules[record.root].syntax, "project-library-unreachable",
             "captured library is not in the application's dependency "
             "closure");
    for (uint32_t index = 0; index < modules.size(); ++index) {
      auto &m = modules[index];
      for (const auto &child : m.syntax.modules) {
        auto p = m.path;
        p.push_back(child.name);
        auto it = paths.find({m.owner, p});
        if (it == paths.end()) {
          fail(child, "source-module-missing",
               "declared module is not captured");
          continue;
        }
        insert(index, child.name,
               {Binding::Kind::Module, it->second,
                llvm::is_contained(m.syntax.exports, child.name)},
               child);
      }
      if (!m.path.empty()) {
        auto p = m.path;
        auto name = p.back();
        p.pop_back();
        auto parent = paths.find({m.owner, p});
        if (parent == paths.end() ||
            llvm::none_of(modules[parent->second].syntax.modules,
                          [&](const auto &d) { return d.name == name; }))
          fail(m.syntax, "source-module-undeclared",
               "captured module is not declared by its parent");
      }
      declarations(m.syntax, [&](const auto &node, auto kind) {
        uint32_t id = context->declarations.size();
        library::QualifiedDecl q{context->owners[m.owner].identity, m.path,
                                 node.name};
        // Existing root spelling remains the application's callable surface.
        // Library/module symbols are identity-derived and never ordinal slots.
        bool nominal = kind == Declaration::Kind::Record ||
                       kind == Declaration::Kind::Enum ||
                       kind == Declaration::Kind::Interface ||
                       kind == Declaration::Kind::Component ||
                       kind == Declaration::Kind::Selection ||
                       kind == Declaration::Kind::Association ||
                       kind == Declaration::Kind::Constant;
        bool builtinCollision =
            nominal && (installedType(node.name) ||
                        !protocol::installedIdentitySort(node.name).empty());
        auto symbol = m.owner == 0 && m.path.empty() && !builtinCollision
                          ? node.name
                          : "src_" + digest(library::identity(q)).substr(0, 40);
        if (auto prefix = reservedPrefix(node.name); prefix) {
          fail(node, "source-name-reserved",
               "'" + node.name + "' begins with '" + *prefix +
                   "', which names only what the compiler generates");
          // Nothing encloses a declaration while declarations are collected,
          // so the refusal marks this one itself.
          // Retain ordinary invalid names for diagnostics. The installed
          // namespace alone also needs an internal noncolliding locator.
          if (*prefix == "__installed_")
            symbol = "src_" + digest(library::identity(q)).substr(0, 40);
          context->unavailable.insert(symbol);
        }
        auto origin = llvm::join(m.path, ".");
        if (!origin.empty())
          origin += ".";
        origin += node.name;
        bool exported = llvm::is_contained(m.syntax.exports, node.name);
        if (!context->symbols.emplace(symbol, id).second) {
          const bool duplicate =
              context->nominalDeclarations.count(library::identity(q));
          fail(node,
               duplicate ? (kind == Declaration::Kind::Relation
                                ? "relation-duplicate-alias"
                                : "source-duplicate-symbol")
                         : "source-symbol-collision",
               duplicate
                   ? "duplicate declaration"
                   : "different declarations have the same emitted symbol");
        }
        context->nominalDeclarations.emplace(library::identity(q), id);
        context->declarations.push_back({std::move(q), kind, m.owner, m.file,
                                         exported, symbol, origin,
                                         node.location});
        insert(index, node.name, {Binding::Kind::Declaration, id, exported},
               node);
      });
      for (const auto &binding : m.syntax.bindings)
        if (protocol::authoringStage(binding.application.contract) !=
            protocol::AuthoringStage::Source)
          fail(binding, "source-operation-stage",
               "operation is not available to ordinary source bindings");
      for (const auto &binding : m.syntax.bindings)
        context->bindingContracts.emplace(
            context->declarations[m.names.at(binding.name).index].symbol,
            binding.application.contract);
      for (auto [i, u] : enumerate(m.syntax.uses))
        insert(index, u.name, {Binding::Kind::Use, uint32_t(i), u.exported}, u);
      if (m.path.empty())
        for (const auto &[name, target] : context->owners[m.owner].dependencies)
          if (m.names.count(name))
            fail(m.syntax, "source-name-duplicate",
                 "dependency alias conflicts with a declaration");
    }
    installDeclarations();
    context->intervals.resize(file);
    for (uint32_t i = 0; i < context->declarations.size(); ++i) {
      const auto &d = context->declarations[i];
      if (d.location)
        context->intervals[d.file].push_back(i);
    }
    for (auto &file : context->intervals)
      llvm::sort(file, [&](auto a, auto b) {
        return context->declarations[a].location->offset <
               context->declarations[b].location->offset;
      });
    allocateOrigins();
    std::vector<unsigned> states(context->owners.size());
    for (uint32_t owner = 0; owner < states.size(); ++owner)
      ownerOrder(owner, states);
    return true;
  }
  void allocateOrigins() {
    // A declaration owns both its root and every emitted component member.
    // Qualify all owners in a collision class before checking explicit claims.
    struct Claim {
      uint32_t declaration;
      std::string suffix;
    };
    std::map<std::string, std::vector<Claim>> claims;
    std::set<uint32_t> explicitOrigins;
    for (const auto &m : modules)
      if (m.owner == 0 && m.path.empty())
        for (const auto &f : m.syntax.functions)
          if (!f.generic && f.explicitOrigin)
            explicitOrigins.insert(m.names.at(f.name).index);
    // Explicit-root emitted names still compete with imported logical origins:
    // downstream closed selectors match both a function's name and its origin.
    // They participate in qualification, but reserve only their explicit
    // origin.
    for (uint32_t i = 0; i < context->declarations.size(); ++i)
      if (context->declarations[i].file != UINT32_MAX)
        claims[context->declarations[i].origin].push_back({i, {}});
    for (const auto &m : modules)
      for (const auto &component : m.syntax.libraryComponents) {
        auto i = m.names.at(component.name).index;
        for (const auto &member : component.functions) {
          componentMembers[i].push_back(member.name);
          claims[context->declarations[i].origin + "." + member.name].push_back(
              {i, "." + member.name});
        }
      }
    std::set<uint32_t> qualify;
    for (const auto &[origin, group] : claims) {
      std::set<uint32_t> owners;
      for (const auto &claim : group)
        owners.insert(context->declarations[claim.declaration].owner);
      if (owners.size() > 1) {
        context->ambiguousOrigins.insert(origin);
        for (const auto &claim : group)
          qualify.insert(claim.declaration);
      }
    }
    for (auto i : qualify) {
      auto &d = context->declarations[i];
      const bool anonymous =
          d.owner == 0 &&
          modules[context->owners[0].root].syntax.libraryIdentities.empty();
      auto qualifier =
          anonymous
              ? std::string("application")
              : "l" + digest(ownerIdentity(d.identity.library)).substr(0, 16);
      d.origin = qualifier + "." + d.origin;
    }
    std::map<std::string, std::string> allocated;
    // The origin of a declaration that emits code (a function, a generic
    // definition or configuration, a component's members, a link or a view)
    // becomes a carrier name, which admission bounds at 128 bytes. A module
    // path that makes one longer is refused here, where the declaration is
    // known; the origins of types, constants and protocols stay in the
    // resolver and are not bounded.
    auto bounded = [&](StringRef origin, const source::Node &node) {
      if (origin.size() > 128)
        fail(node, "source-origin-limit",
             "logical origin '" + origin +
                 "' is longer than the 128 bytes a carrier name admits");
    };
    auto emitsCode = [](Declaration::Kind kind) {
      using K = Declaration::Kind;
      return kind == K::Function || kind == K::Configuration ||
             kind == K::Component || kind == K::Link || kind == K::View;
    };
    auto claim = [&](StringRef origin, StringRef key,
                     const source::Node &node) {
      auto [it, inserted] = allocated.emplace(origin.str(), key.str());
      if (!inserted && it->second != key)
        fail(node, "source-origin-collision",
             "different declarations claim logical origin '" + origin + "'");
    };
    for (const auto &[old, group] : claims)
      for (const auto &c : group) {
        if (explicitOrigins.count(c.declaration))
          continue;
        const auto &d = context->declarations[c.declaration];
        if (emitsCode(d.kind))
          bounded(d.origin + c.suffix, source::Node{d.location});
        claim(d.origin + c.suffix, library::identity(d.identity) + c.suffix,
              source::Node{d.location});
      }
    // Relation members intentionally share their exact relation-content origin.
    // An ordinary declaration cannot claim that generated origin.
    for (const auto &m : modules)
      for (const auto &r : m.syntax.relations) {
        auto key = relation::identity(r);
        claim("Relation_" + key, "relation:" + key, r);
      }
    for (const auto &m : modules)
      for (const auto &f : m.syntax.functions) {
        if (!f.explicitOrigin || !f.origin)
          continue;
        if (m.owner != 0 || !m.path.empty()) {
          fail(f, "source-origin-owner",
               "explicit ordinary origins belong only to the application root");
          continue;
        }
        auto &d = context->declarations[m.names.at(f.name).index];
        bounded(f.origin->definition, f);
        claim(f.origin->definition,
              "explicit-application:" + f.origin->definition, f);
        if (!f.generic)
          d.origin = f.origin->definition;
      }
  }
  void publicSignatures() {
    // Propagate only signature dependencies. A wrapper's private body is not
    // its public contract, while a private record/interface in its signature
    // is.
    const auto size = context->declarations.size();
    std::vector<std::vector<uint32_t>> dependents(size);
    for (const auto &[owner, references] : signatureReferences)
      for (auto target : references)
        dependents[target].push_back(owner);
    std::vector<std::optional<uint32_t>> leak(size);
    std::vector<uint32_t> queue;
    for (uint32_t i = 0; i < size; ++i) {
      const auto &d = context->declarations[i];
      if (!d.exported && (d.kind == Declaration::Kind::Record ||
                          d.kind == Declaration::Kind::Enum ||
                          d.kind == Declaration::Kind::Interface ||
                          d.kind == Declaration::Kind::Association ||
                          d.kind == Declaration::Kind::Relation)) {
        leak[i] = i;
        queue.push_back(i);
      }
    }
    for (size_t i = 0; i < queue.size(); ++i)
      for (auto dependent : dependents[queue[i]])
        if (!leak[dependent]) {
          leak[dependent] = leak[queue[i]];
          queue.push_back(dependent);
        }
    for (uint32_t i = 0; i < size; ++i)
      if (context->declarations[i].exported && leak[i]) {
        const auto &d = context->declarations[i];
        fail(source::Node{d.location}, "source-private-signature",
             "public signature exposes private nominal declaration '" +
                 context->declarations[*leak[i]].identity.name + "'");
      }
  }
  void exported(uint32_t module, std::set<uint32_t> &out,
                std::set<uint32_t> &visited) {
    if (!visited.insert(module).second)
      return;
    for (const auto &[name, binding] : modules[module].names) {
      if (!binding.exported)
        continue;
      auto target = binding.kind == Binding::Kind::Use
                        ? use(module, binding.index)
                        : std::optional<Binding>(binding);
      if (!target)
        continue;
      if (target->kind == Binding::Kind::Declaration)
        out.insert(target->index);
      else if (target->kind == Binding::Kind::Module)
        exported(target->index, out, visited);
    }
  }
  void environments() {
    context->available.resize(context->owners.size());
    std::vector<std::set<uint32_t>> publicNames(context->owners.size());
    for (uint32_t i = 0; i < publicNames.size(); ++i) {
      std::set<uint32_t> visited;
      exported(context->owners[i].root, publicNames[i], visited);
    }
    for (uint32_t i = 0; i < context->owners.size(); ++i) {
      auto &available = context->available[i];
      for (uint32_t j = 0; j < context->declarations.size(); ++j)
        if (context->declarations[j].owner == i)
          available.insert(j);
      for (const auto &[alias, dependency] : context->owners[i].dependencies)
        available.insert(publicNames[dependency].begin(),
                         publicNames[dependency].end());
      // Follow only actually exposed signature dependencies. Private helper
      // bodies and unrelated dependencies of a dependency do not enter here.
      std::vector<uint32_t> queue(available.begin(), available.end());
      for (size_t n = 0; n < queue.size(); ++n)
        for (auto dependency : signatureReferences[queue[n]])
          if (available.insert(dependency).second)
            queue.push_back(dependency);
    }
    std::vector<uint32_t> operators;
    for (const auto &m : modules)
      for (const auto &f : m.syntax.functions)
        if (f.operatorHook)
          if (const auto *d = context->lookup(f.name))
            operators.push_back(d - context->declarations.data());
    for (uint32_t request = 0; request < modules.size(); ++request) {
      const auto &m = modules[request];
      if (m.file == UINT32_MAX)
        continue;
      auto visible = publicNames[m.owner];
      for (const auto &[alias, dependency] :
           context->owners[m.owner].dependencies)
        visible.insert(publicNames[dependency].begin(),
                       publicNames[dependency].end());
      // Walk callable paths using the resolved module graph. Internal operator
      // discovery must not spend the authored name-resolution budget, report
      // module-level lookup errors, or reinterpret opaque module names.
      std::set<uint32_t> visited;
      std::vector<uint32_t> pending{context->owners[m.owner].root};
      while (!pending.empty()) {
        auto module = pending.back();
        pending.pop_back();
        if (!visited.insert(module).second)
          continue;
        for (const auto &[name, binding] : modules[module].names) {
          if (!binding.exported && !inside(request, module))
            continue;
          auto target = binding;
          if (binding.kind == Binding::Kind::Use) {
            auto alias = aliases.find({module, binding.index});
            if (alias == aliases.end())
              continue;
            target = alias->second;
          }
          if (target.kind == Binding::Kind::Declaration && target.exact())
            visible.insert(target.index);
          else if (target.kind == Binding::Kind::Module &&
                   modules[target.index].owner == m.owner)
            pending.push_back(target.index);
        }
      }
      for (auto index : operators) {
        const auto &d = context->declarations[index];
        if (visible.count(index))
          context->sourceOperators[m.file].insert(d.symbol);
      }
    }
  }

  std::optional<syntax::Content> recover(const syntax::Module &out) {
    if (diagnostics.empty())
      return {};
    // Only name/dependency failures permit independent recovery. A malformed
    // identity, duplicate declaration, or exhausted budget makes the project
    // graph itself unavailable; do not choose an arbitrary interpretation.
    for (const auto &d : diagnostics) {
      StringRef code = d.code;
      if (code != "source-name-unresolved" && code != "source-name-private" &&
          code != "source-name-kind" && code != "source-name-reserved" &&
          code != "source-dependency-missing" &&
          code != "source-private-signature" &&
          code != "source-private-reexport" && code != "source-import-cycle")
        return {};
    }
    // Operators have no authored callee reference. Recover their dependencies
    // from known operand heads before removing the failed declarations.
    auto operatorReferences = OperatorRecovery(out, *context, maxWork).record();
    if (!operatorReferences)
      return {};
    // Every transitive referrer of an unavailable declaration is unavailable.
    // Walk the reverse references once so the work is linear in the
    // references whatever order the declarations appear in.
    std::map<StringRef, std::vector<StringRef>> referrers;
    for (const auto &r : context->references)
      referrers[r.target].push_back(r.source);
    // Diagnostic-only edges must not escape into checking or provenance.
    for (const auto &r : *operatorReferences)
      referrers[r.target].push_back(r.source);
    std::vector<std::string> pending(context->unavailable.begin(),
                                     context->unavailable.end());
    while (!pending.empty()) {
      auto target = std::move(pending.back());
      pending.pop_back();
      auto found = referrers.find(target);
      if (found == referrers.end())
        continue;
      for (auto source : found->second)
        if (context->unavailable.insert(source.str()).second)
          pending.push_back(source.str());
    }
    auto filtered = out;
    declarationLists(filtered, [&](auto &items, auto) {
      llvm::erase_if(items, [&](const auto &d) {
        return context->unavailable.count(d.name);
      });
    });
    return syntax::Content(std::move(filtered));
  }

public:
  explicit Resolver(ProjectInput input)
      : context(std::make_shared<Context>(std::move(input))) {}
  Result run() {
    syntax::Module out;
    if (!collect())
      return {standalone ? std::move(*standalone)
                         : syntax::Content(std::move(out)),
              context, std::move(diagnostics), syntaxPartial, std::nullopt};
    // Diagnose all imports, even unused ones; no dependency body is unchecked
    // merely because it is unreachable from an application entry.
    for (uint32_t i = 0; i < modules.size(); ++i)
      for (uint32_t j = 0; j < modules[i].syntax.uses.size(); ++j)
        use(i, j);
    for (const auto &[site, binding] : aliases) {
      auto &visible = context->installedModules[modules[site.first].file];
      if (binding.kind == Binding::Kind::Declaration) {
        const auto &d = context->declarations[binding.index];
        if (d.kind == Declaration::Kind::LogicalType ||
            d.kind == Declaration::Kind::Operation ||
            d.kind == Declaration::Kind::Capability)
          visible.insert("zkc::" + llvm::join(d.identity.module, "::"));
      } else if (binding.kind == Binding::Kind::Module && installedRoot &&
                 modules[binding.index].owner ==
                     modules[*installedRoot].owner) {
        const auto &prefix = modules[binding.index].path;
        for (const auto &m : modules)
          if (m.owner == modules[*installedRoot].owner &&
              m.path.size() >= prefix.size() &&
              std::equal(prefix.begin(), prefix.end(), m.path.begin()))
            visible.insert("zkc::" + llvm::join(m.path, "::"));
      }
    }
    memberSurfaces();
    for (auto [key, binding] : aliases)
      if (!binding.exact() &&
          !authorizes(binding, ReferenceKind::Call,
                      modules[key.first].syntax.uses[key.second]))
        fail(modules[key.first].syntax.uses[key.second],
             "source-name-unresolved",
             "import does not name a generated helper");
    for (uint32_t i = 0; i < modules.size(); ++i) {
      ModuleResolver resolver;
      resolver.path = [&, i](const syntax::Path &path, const source::Node &n,
                             ReferenceKind kind, bool signature) {
        return reference(i, path, n, kind, signature);
      };
      resolver.exact = [&](StringRef value, const source::Node &n,
                           ReferenceKind kind) { exact(value, n, kind); };
      // A definition's own name is exact, never a path.
      resolver.definition = [&,
                             i](StringRef name) -> std::optional<std::string> {
        auto found = modules[i].names.find(name.str());
        if (found == modules[i].names.end() ||
            found->second.kind != Binding::Kind::Declaration)
          return std::nullopt;
        return context->declarations[found->second.index].symbol;
      };
      qualify(modules[i].syntax, *context, resolver);
    }
    publicSignatures();
    environments();
    // Retain the resolved name graph. Construction indexes it only when a
    // checked source snapshot is used with a descriptor; ordinary checking
    // does not acquire construction selector limits or diagnostics.
    context->selectorWork = work;
    context->componentMembers = componentMembers;
    context->selectorScopes.resize(modules.size());
    for (uint32_t i = 0; i < modules.size(); ++i) {
      auto &scope = context->selectorScopes[i];
      scope.location = modules[i].syntax.location;
      for (const auto &[name, binding] : modules[i].names) {
        // All imports were resolved above. Failed imports have no cache entry;
        // never resolve them again merely to retain selector lookup data.
        auto alias = aliases.find({i, binding.index});
        auto target =
            binding.kind != Binding::Kind::Use ? std::optional<Binding>(binding)
            : alias == aliases.end() ? std::nullopt
                                     : std::optional<Binding>(alias->second);
        scope.names.push_back(
            {name, binding.exported,
             target && target->kind == Binding::Kind::Module,
             target ? std::optional<uint32_t>(target->index) : std::nullopt});
      }
    }
    // Root order is deterministic by exact owner identity, then module path.
    // Dependency traversal order affects checking, not declaration identity.
    std::vector<uint32_t> ordered;
    for (uint32_t i = 0; i < modules.size(); ++i)
      ordered.push_back(i);
    llvm::sort(ordered, [&](auto a, auto b) {
      auto ka = ownerIdentity(context->owners[modules[a].owner].identity);
      auto kb = ownerIdentity(context->owners[modules[b].owner].identity);
      return std::tie(ka, modules[a].path) < std::tie(kb, modules[b].path);
    });
    out.location = modules[context->owners[0].root].syntax.location;
    for (auto i : ordered) {
      auto &m = modules[i];
      if (m.owner != 0)
        m.syntax.entries.clear(); // Imports never introduce execution roots.
      append(out, std::move(m.syntax));
    }
    syntax::inferCaptures(out);
    auto recovered = recover(out);
    return {std::move(out), context, std::move(diagnostics), syntaxPartial,
            std::move(recovered)};
  }
};
} // namespace
Result resolve(const ProjectInput &input) { return Resolver(input).run(); }
} // namespace zkc::frontend::resolution
