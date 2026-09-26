#include "Project.h"
#include "zkc/Support/Json.h"
using namespace llvm;
namespace zkc::frontend::resolution {
namespace {
class Indexer {
  const Context &context;
  SelectorIndex index;
  std::optional<Diagnostic> problem;
  size_t work;
  static constexpr size_t maxWork = 262144;
  void fail(const source::Node &node, StringRef code, const Twine &message) {
    if (!problem)
      problem = Diagnostic{code.str(), message.str(), node.location};
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
  ArrayRef<std::string> members(uint32_t i) const {
    auto found = context.componentMembers.find(i);
    return found == context.componentMembers.end()
               ? ArrayRef<std::string>()
               : ArrayRef<std::string>(found->second);
  }
  static bool drawSelectable(Declaration::Kind kind) {
    using K = Declaration::Kind;
    switch (kind) {
    case K::Function:
    case K::Protocol:
    case K::Component:
    case K::Selection:
    case K::Link:
    case K::View:
    case K::Configuration:
      return true;
    default:
      return false;
    }
  }
  void selectors(uint32_t module, StringRef prefix, bool publicOnly,
                 std::set<uint32_t> visited = {}) {
    if (!visited.insert(module).second ||
        !spend(source::Node{context.selectorScopes[module].location}))
      return;
    for (const auto &binding : context.selectorScopes[module].names) {
      if (!spend(source::Node{context.selectorScopes[module].location}))
        return;
      if (publicOnly && !binding.exported)
        continue;
      const auto &name = binding.name;
      auto target = binding.target;
      if (!target)
        continue;
      auto path = prefix.empty() ? name : (prefix + "." + name).str();
      if (path.size() > 4096) {
        fail(source::Node{context.selectorScopes[module].location},
             "source-resolution-limit",
             "construction selector path exceeds 4096 bytes");
        work = maxWork + 1;
        return;
      }
      if (binding.module)
        selectors(*target, path, true, visited);
      else if (!binding.module) {
        const auto kind = context.declarations[*target].kind;
        const bool entry = kind == Declaration::Kind::Entry;
        if (!entry && !drawSelectable(kind))
          continue;
        auto &entries = entry ? index.entrySelectors : index.selectors;
        if (!entry && entries.size() >= 32768 && !entries.count(path)) {
          fail(source::Node{context.selectorScopes[module].location},
               "source-resolution-limit",
               "construction selector budget exhausted");
          work = maxWork + 1;
          return;
        }
        auto [it, inserted] = entries.emplace(path, *target);
        if (!inserted && it->second != *target)
          fail(source::Node{context.selectorScopes[module].location},
               "source-selector-ambiguity",
               "construction selector names different declarations: '" + path +
                   "'");
      }
    }
  }
  void selectorAmbiguities() {
    // Index closed spellings once, including whole component member origins.
    // Source paths may not silently capture another owner's closed selector.
    std::map<std::string, std::set<uint32_t>> closed;
    auto add = [&](StringRef name, uint32_t declaration) {
      closed[name.str()].insert(context.declarations[declaration].owner);
    };
    for (uint32_t i = 0; i < context.declarations.size(); ++i) {
      const auto &d = context.declarations[i];
      if (!drawSelectable(d.kind))
        continue;
      if (!spend(source::Node{d.location}))
        return;
      add(d.symbol, i);
      add(d.origin, i);
      for (const auto &member : members(i)) {
        if (!spend(source::Node{d.location}))
          return;
        add(d.symbol + "." + member, i);
        add(d.origin + "." + member, i);
      }
    }
    auto check = [&](StringRef path, uint32_t declaration) {
      auto found = closed.find(path.str());
      if (found == closed.end())
        return;
      const auto owner = context.declarations[declaration].owner;
      if (found->second.size() > 1 || !found->second.count(owner))
        index.ambiguousOrigins.insert(path.str());
    };
    for (const auto &[path, target] : index.selectors) {
      if (!spend(source::Node{context.declarations[target].location}))
        return;
      check(path, target);
      for (const auto &member : members(target)) {
        if (!spend(source::Node{context.declarations[target].location}))
          return;
        check(path + "." + member, target);
      }
    }
  }

public:
  explicit Indexer(const Context &context)
      : context(context), work(context.selectorWork) {
    index.ambiguousOrigins = context.ambiguousOrigins;
  }
  Expected<SelectorIndex> run() {
    if (!context.carrier && !context.owners.empty()) {
      selectors(context.owners[0].root, {}, false);
      for (const auto &[alias, target] : context.owners[0].dependencies)
        selectors(context.owners[target].root, alias, true);
      selectorAmbiguities();
    }
    if (problem)
      return diagnostic(context.input, *problem);
    return std::move(index);
  }
};
} // namespace
Expected<SelectorIndex> constructionSelectors(const Context &context) {
  return Indexer(context).run();
}
} // namespace zkc::frontend::resolution
