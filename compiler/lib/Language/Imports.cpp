#include "Checker.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
bool Checker::moduleContracts() {
  // Interface membership determines the public contract before imports are
  // authorized. Full type/effect conformance follows signature formation.
  for (auto id : moduleIds) {
    auto &module = output.declarations[id.index];
    auto &written = *sources[id.index];
    if (!written.definition)
      continue;
    auto target =
        resolve(module, written.definition->name, written.definition->span);
    if (!target)
      return false;
    const auto &contract = output.declarations[target->index];
    if (contract.kind != Declaration::Kind::Interface)
      return types.fail("source.conformance",
                        "module must implement an interface", module.span);
    if (!types.charge(contract.members.size() + module.members.size(),
                      module.span))
      return false;
    for (auto required : contract.members) {
      const auto &member = output.declarations[required.index];
      auto found = visible[id.index].find(member.name);
      if (found == visible[id.index].end())
        continue; // The conformance checker reports missing members.
      auto &provided = output.declarations[found->second.target.index];
      if (!provided.parent || provided.parent->index != id.index)
        continue; // Imports do not implement an authored interface member.
      provided.isPublic = true;
      found->second.isPublic = true;
    }
  }
  return true;
}
bool Checker::imports() {
  const auto count = sources.size();
  std::vector<std::vector<unsigned>> bindingState(count), bindingHeight(count);
  std::vector<std::vector<std::vector<ModuleLookup>>> routes(count);
  std::vector<std::map<std::string, std::vector<unsigned>>> candidates(count);
  for (auto module : moduleIds) {
    const auto id = module.index;
    const auto &imports = sources[id]->imports;
    if (!types.charge(imports.size(), sources[id]->span))
      return false;
    bindingState[id].resize(imports.size());
    bindingHeight[id].resize(imports.size());
    routes[id].resize(imports.size());
    for (unsigned i = 0; i < imports.size(); ++i) {
      const auto &import = imports[i];
      if (!types.charge(import.names.size() + 1, import.span))
        return false;
      for (const auto &name : import.names)
        candidates[id][name].push_back(i);
      if (import.alias)
        candidates[id][*import.alias].push_back(i);
    }
  }
  auto lookup = [&](const Declaration &context, DeclarationId owner,
                    StringRef name, Span span) {
    auto selected = member(context, owner, name, span);
    if (!selected && !types.diagnostic)
      types.fail("source.import", "unknown import: " + name, span);
    return selected;
  };
  // Resolve bindings without loading a target module's unrelated imports.
  // This graph and the completed module graph have separate depth budgets.
  unsigned bindingDepth = 0;
  std::vector<std::pair<unsigned, unsigned>> bindingStack;
  auto loadImport = [&](unsigned id, unsigned index) -> bool {
    auto &import = sources[id]->imports[index];
    const auto &context = output.declarations[id];
    if (!types.charge(1, import.span))
      return false;
    if (bindingDepth >= work.limits.importDepth ||
        bindingHeight[id][index] > work.limits.importDepth - bindingDepth)
      return types.fail("source.limit", "import binding depth exceeded",
                        import.span);
    auto propagateHeight = [&] {
      if (!bindingStack.empty()) {
        auto [owner, position] = bindingStack.back();
        bindingHeight[owner][position] = std::max(
            bindingHeight[owner][position], bindingHeight[id][index] + 1);
      }
    };
    if (bindingState[id][index] == 2) {
      propagateHeight();
      return true;
    }
    if (bindingState[id][index] == 1)
      return types.fail("source.cycle", "cyclic import bindings", import.span);
    bindingState[id][index] = 1;
    bindingHeight[id][index] = 1;
    ++bindingDepth;
    bindingStack.emplace_back(id, index);
    auto selected =
        resolve(context, import.module, import.span, false, &routes[id][index]);
    if (!selected ||
        output.declarations[selected->index].kind != Declaration::Kind::Module)
      return types.diagnostic
                 ? false
                 : types.fail("source.import",
                              "import does not name a captured module: " +
                                  import.module,
                              import.span);
    import.target = *selected;
    auto bind = [&](StringRef name, DeclarationId target) {
      if (!types.charge(1, import.span))
        return false;
      auto [position, inserted] = visible[id].emplace(
          name.str(), ModuleBinding{target, import.span, import.isPublic});
      if (!inserted && position->second.target.index != target.index)
        return types.fail("source.duplicate",
                          "import conflicts with visible name: " + name,
                          import.span);
      position->second.isPublic |= import.isPublic;
      return true;
    };
    for (const auto &name : import.names) {
      auto member = lookup(context, *selected, name, import.span);
      if (!member || !bind(name, *member))
        return false;
    }
    if (import.alias && !bind(*import.alias, *selected))
      return false;
    bindingStack.pop_back();
    --bindingDepth;
    bindingState[id][index] = 2;
    propagateHeight();
    return true;
  };
  loadBinding = [&](DeclarationId module, StringRef name) {
    // Authored declarations already fix their binding. Imports still check
    // conflicts when loaded; cached imports retain their dependency heights.
    auto existing = visible[module.index].find(name.str());
    if (existing != visible[module.index].end()) {
      const auto &target = output.declarations[existing->second.target.index];
      if (target.parent && target.parent->index == module.index &&
          target.name == name)
        return true;
    }
    auto found = candidates[module.index].find(name.str());
    if (found == candidates[module.index].end())
      return true;
    for (auto index : found->second) {
      // An import's own names are not in scope while resolving that import.
      if (!bindingStack.empty() &&
          bindingStack.back() == std::make_pair(module.index, index))
        continue;
      if (!loadImport(module.index, index))
        return false;
    }
    return true;
  };
  for (auto module : moduleIds)
    for (unsigned i = 0; i < sources[module.index]->imports.size(); ++i)
      if (!loadImport(module.index, i))
        return false;
  loadBinding = {};

  // All targets are now immutable. Validate and order the module graph before
  // propagating notation exports; loading order cannot change name resolution.
  std::vector<unsigned> order, state(count), height(count);
  auto visit = [&](auto &&self, unsigned id, unsigned depth) -> bool {
    auto span = sources[id]->span;
    if (!types.charge(1, span))
      return false;
    if (depth >= work.limits.importDepth ||
        height[id] > work.limits.importDepth - depth)
      return types.fail("source.limit", "import depth limit exceeded", span);
    if (state[id] == 2)
      return true;
    if (state[id] == 1)
      return types.fail("source.cycle", "cyclic module imports", span);
    state[id] = 1;
    height[id] = 1;
    for (const auto &import : sources[id]->imports) {
      auto target = import.target->index;
      if (!self(self, target, depth + 1))
        return false;
      height[id] = std::max(height[id], height[target] + 1);
    }
    state[id] = 2;
    order.push_back(id);
    return true;
  };
  for (auto module : moduleIds)
    if (!visit(visit, module.index, 0))
      return false;

  if (!moduleContracts())
    return false;
  checkingVisibility = true;
  for (auto module : moduleIds) {
    auto id = module.index;
    const auto &context = output.declarations[id];
    for (unsigned i = 0; i < sources[id]->imports.size(); ++i) {
      const auto &import = sources[id]->imports[i];
      // Authorize the selected route, without resolving its head again through
      // the names introduced by this same import.
      for (const auto &step : routes[id][i])
        if (!lookup(context, step.owner, step.name, import.span))
          return false;
      auto exportable = [&](DeclarationId declaration) {
        return !import.isPublic ||
               output.declarations[declaration.index].isPublic ||
               types.fail(
                   "source.private",
                   "a public import cannot publish a private declaration",
                   import.span, {output.declarations[declaration.index].span});
      };
      if (import.alias && !exportable(*import.target))
        return false;
      for (const auto &name : import.names) {
        auto selected = lookup(context, *import.target, name, import.span);
        if (!selected || !exportable(*selected))
          return false;
      }
    }
  }

  visibleOperators.resize(count);
  exportedOperators.resize(count);
  auto importNotation = [&](unsigned id, const Import &import) {
    const auto target = import.target->index;
    std::set<std::string> selectedOperators(import.operators.begin(),
                                            import.operators.end());
    std::set<std::string> selectedNotations(import.notations.begin(),
                                            import.notations.end());
    std::set<std::string> selectedReductions(import.reductions.begin(),
                                             import.reductions.end());
    bool selectedIndexing = import.indexing;
    for (auto site : exportedOperators[target]) {
      if (!types.charge(1, import.span))
        return false;
      const auto &binding = sources[site.first]->operators[site.second];
      const auto &symbol = binding.symbol;
      bool indexing =
          binding.notation &&
          binding.notation->position == NotationDescriptor::Position::Index;
      bool delimited = !indexing && !binding.holes.empty();
      bool reduction =
          binding.notation &&
          binding.notation->position == NotationDescriptor::Position::Reduction;
      if (!import.alias &&
          !(indexing ? import.indexing
                     : is_contained(reduction   ? import.reductions
                                    : delimited ? import.notations
                                                : import.operators,
                                    symbol)))
        continue;
      if (indexing)
        selectedIndexing = false;
      (reduction   ? selectedReductions
       : delimited ? selectedNotations
                   : selectedOperators)
          .erase(symbol);
      visibleOperators[id].push_back(site);
      if (import.isPublic)
        exportedOperators[id].push_back(site);
    }
    if (selectedIndexing)
      return types.fail("source.import", "module does not export indexing []",
                        import.span);
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
    return true;
  };
  for (auto id : order) {
    const auto &source = *sources[id];
    for (unsigned i = 0; i < source.operators.size(); ++i) {
      visibleOperators[id].emplace_back(id, i);
      if (source.operators[i].isPublic)
        exportedOperators[id].emplace_back(id, i);
    }
    for (const auto &import : source.imports)
      if (!importNotation(id, import))
        return false;
    for (auto *sites : {&visibleOperators[id], &exportedOperators[id]}) {
      llvm::sort(*sites);
      sites->erase(std::unique(sites->begin(), sites->end()), sites->end());
    }
  }
  // Lexical notation is inherited without publishing it from child modules.
  for (auto id : moduleIds) {
    const auto &module = output.declarations[id.index];
    if (!module.parent)
      continue;
    auto parent = module.parent->index;
    if (!types.charge(visibleOperators[parent].size(), module.span))
      return false;
    visibleOperators[id.index].insert(visibleOperators[id.index].end(),
                                      visibleOperators[parent].begin(),
                                      visibleOperators[parent].end());
  }
  if (auto prelude = modules.find("zkc::prelude"); prelude != modules.end()) {
    const auto id = prelude->second.index;
    if (!sources[id]->imports.empty())
      return types.fail("source.import",
                        "installed prelude cannot import captured modules",
                        sources[id]->imports.front().span);
    for (auto module : moduleIds) {
      auto i = module.index;
      if (i == id)
        continue;
      if (!types.charge(exportedOperators[id].size(),
                        output.declarations[i].span))
        return false;
      visibleOperators[i].insert(visibleOperators[i].end(),
                                 exportedOperators[id].begin(),
                                 exportedOperators[id].end());
    }
  }
  for (auto module : moduleIds) {
    auto &sites = visibleOperators[module.index];
    llvm::sort(sites);
    sites.erase(std::unique(sites.begin(), sites.end()), sites.end());
  }
  return true;
}
} // namespace zkc::language::detail
