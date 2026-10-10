#include "Checker.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
bool Checker::imports() {
  const auto count = syntax.size();
  aliases.resize(count);
  exportedAliases.resize(count);
  exportedNames.resize(count);
  visibleOperators.resize(count);
  exportedOperators.resize(count);
  std::vector<std::vector<unsigned>> edges(count);
  for (const auto &module : syntax) {
    auto id = module.id.index;
    for (const auto &[name, declaration] : visible[id])
      if (output.declarations[declaration.index].isPublic)
        exportedNames[id].emplace(name, declaration);
    for (unsigned i = 0; i < module.operators.size(); ++i) {
      visibleOperators[id].emplace_back(id, i);
      if (module.operators[i].isPublic)
        exportedOperators[id].emplace_back(id, i);
    }
    for (const auto &import : module.imports) {
      auto target = modules.find(import.module);
      if (target == modules.end())
        return types.fail("source.import",
                          "module was not explicitly captured: " +
                              import.module,
                          import.span);
      edges[id].push_back(target->second.index);
    }
    llvm::sort(edges[id]);
  }
  std::vector<unsigned> state(count), height(count), order;
  std::function<bool(unsigned, unsigned)> visit = [&](unsigned id,
                                                      unsigned depth) {
    Span span{ModuleId{id}, 0, 0};
    if (!types.charge(1, span))
      return false;
    if (depth > work.limits.importDepth)
      return types.fail("source.limit", "import depth limit exceeded", span);
    if (state[id] == 1)
      return types.fail("source.cycle", "cyclic module imports", span);
    if (state[id] == 2)
      return depth - 1 + height[id] <= work.limits.importDepth ||
             types.fail("source.limit", "import depth limit exceeded", span);
    state[id] = 1;
    height[id] = 1;
    for (auto edge : edges[id]) {
      if (!visit(edge, depth + 1))
        return false;
      height[id] = std::max(height[id], height[edge] + 1);
    }
    state[id] = 2;
    order.push_back(id);
    return true;
  };
  for (unsigned i = 0; i < count; ++i)
    if (!visit(i, 1))
      return false;
  importOrder = order;
  for (auto id : order) {
    for (const auto &import : syntax[id].imports) {
      const auto target = modules.at(import.module).index;
      auto name = [&](StringRef spelling,
                      std::optional<DeclarationId> declaration,
                      std::optional<ModuleId> module) {
        const auto key = spelling.str();
        if (!types.charge(1, import.span))
          return false;
        if (declaration) {
          if (aliases[id].count(key))
            return types.fail("source.duplicate",
                              "import conflicts with module alias: " + spelling,
                              import.span);
          auto [position, inserted] = visible[id].emplace(key, *declaration);
          if (!inserted && position->second.index != declaration->index)
            return types.fail("source.duplicate",
                              "import conflicts with visible name: " + spelling,
                              import.span);
          if (import.isPublic)
            exportedNames[id].emplace(key, *declaration);
        } else {
          if (visible[id].count(key))
            return types.fail("source.duplicate",
                              "module alias conflicts with visible name: " +
                                  spelling,
                              import.span);
          auto [position, inserted] = aliases[id].emplace(key, *module);
          if (!inserted && position->second.index != module->index)
            return types.fail("source.duplicate",
                              "conflicting module aliases: " + spelling,
                              import.span);
          if (import.isPublic)
            exportedAliases[id].emplace(key, *module);
        }
        return true;
      };
      for (const auto &selected : import.names) {
        auto declaration = exportedNames[target].find(selected);
        auto alias = exportedAliases[target].find(selected);
        if (declaration != exportedNames[target].end()) {
          if (!name(selected, declaration->second, {}))
            return false;
        } else if (alias != exportedAliases[target].end()) {
          if (!name(selected, {}, alias->second))
            return false;
        } else {
          if (auto found = visible[target].find(selected);
              found != visible[target].end())
            return types.fail("source.private",
                              "cannot import private declaration: " + selected,
                              import.span,
                              {output.declarations[found->second.index].span});
          return types.fail("source.import",
                            "unknown public import: " + selected, import.span);
        }
      }
      if (import.alias && !name(*import.alias, {}, ModuleId{target}))
        return false;
      std::set<std::string> selectedOperators(import.operators.begin(),
                                              import.operators.end());
      std::set<std::string> selectedNotations(import.notations.begin(),
                                              import.notations.end());
      std::set<std::string> selectedReductions(import.reductions.begin(),
                                               import.reductions.end());
      for (auto site : exportedOperators[target]) {
        if (!types.charge(1, import.span))
          return false;
        const auto &binding = syntax[site.first].operators[site.second];
        const auto &symbol = binding.symbol;
        bool delimited = !binding.holes.empty();
        bool reduction =
            binding.notation && binding.notation->position ==
                                    NotationDescriptor::Position::Reduction;
        if (!import.alias && !is_contained(reduction   ? import.reductions
                                           : delimited ? import.notations
                                                       : import.operators,
                                           symbol))
          continue;
        (reduction   ? selectedReductions
         : delimited ? selectedNotations
                     : selectedOperators)
            .erase(symbol);
        visibleOperators[id].push_back(site);
        if (import.isPublic)
          exportedOperators[id].push_back(site);
      }
      if (!selectedReductions.empty())
        return types.fail("source.import",
                          "module does not export reduction " +
                              *selectedReductions.begin(),
                          import.span);
      if (!selectedNotations.empty())
        return types.fail("source.import",
                          "module does not export notation " +
                              *selectedNotations.begin(),
                          import.span);
      if (!selectedOperators.empty())
        return types.fail("source.import",
                          "module does not export operator " +
                              *selectedOperators.begin(),
                          import.span);
    }
    for (auto *sites : {&visibleOperators[id], &exportedOperators[id]}) {
      llvm::sort(*sites);
      sites->erase(std::unique(sites->begin(), sites->end()), sites->end());
    }
  }
  if (auto prelude = modules.find("zkc::prelude"); prelude != modules.end()) {
    const auto id = prelude->second.index;
    if (!syntax[id].imports.empty())
      return types.fail("source.import",
                        "installed prelude cannot import captured modules",
                        syntax[id].imports.front().span);
    for (unsigned i = 0; i < count; ++i) {
      if (i == id)
        continue;
      if (!types.charge(exportedOperators[id].size(), Span{ModuleId{i}, 0, 0}))
        return false;
      visibleOperators[i].insert(visibleOperators[i].end(),
                                 exportedOperators[id].begin(),
                                 exportedOperators[id].end());
      llvm::sort(visibleOperators[i]);
      visibleOperators[i].erase(
          std::unique(visibleOperators[i].begin(), visibleOperators[i].end()),
          visibleOperators[i].end());
    }
  }
  return true;
}

std::optional<DeclarationId> Checker::moduleMember(ModuleId module,
                                                   StringRef path, Span span,
                                                   unsigned depth) {
  if (!types.charge(1, span))
    return {};
  if (depth > work.limits.importDepth) {
    types.fail("source.limit", "qualified module alias depth exceeded", span);
    return {};
  }
  auto [head, tail] = path.split("::");
  if (auto alias = exportedAliases[module.index].find(head.str());
      alias != exportedAliases[module.index].end())
    return moduleMember(alias->second, tail, span, depth + 1);
  auto found = exportedNames[module.index].find(head.str());
  if (found == exportedNames[module.index].end())
    return {};
  auto result = found->second;
  while (!tail.empty()) {
    auto [name, rest] = tail.split("::");
    const auto &members = output.declarations[result.index].members;
    if (!types.charge(members.size() + 1, span))
      return {};
    auto member = llvm::find_if(members, [&, name = name](DeclarationId id) {
      return output.declarations[id.index].name == name &&
             !output.declarations[id.index].anonymous;
    });
    if (member == members.end())
      return {};
    result = *member;
    tail = rest;
  }
  return result;
}
} // namespace zkc::language::detail
