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
  visibleOperators.resize(count);
  exportedOperators.resize(count);
  for (auto module : moduleIds) {
    auto id = module.index;
    const auto &source = *sources[id];
    for (unsigned i = 0; i < source.operators.size(); ++i) {
      visibleOperators[id].emplace_back(id, i);
      if (source.operators[i].isPublic)
        exportedOperators[id].emplace_back(id, i);
    }
  }
  std::vector<unsigned> state(count), height(count);
  unsigned depth = 0;
  loadImports = [&](DeclarationId module) {
    const auto id = module.index;
    const auto &context = output.declarations[id];
    if (!types.charge(1, context.span))
      return false;
    if (depth >= work.limits.importDepth ||
        height[id] > work.limits.importDepth - depth)
      return types.fail("source.limit", "import depth limit exceeded",
                        context.span);
    // Lexical lookup may consult the scope currently binding an import.
    // Only an actual import edge back into that scope is a cycle.
    if (state[id] == 1)
      return true;
    if (state[id] == 2)
      return true;
    state[id] = 1;
    ++depth;
    height[id] = 1;
    for (auto &import : sources[id]->imports) {
      auto selected = resolve(context, import.module, import.span, false);
      if (!selected || output.declarations[selected->index].kind !=
                           Declaration::Kind::Module)
        return types.diagnostic
                   ? false
                   : types.fail("source.import",
                                "import does not name a captured module: " +
                                    import.module,
                                import.span);
      import.target = *selected;
      const auto target = selected->index;
      if (state[target] == 1)
        return types.fail("source.cycle", "cyclic module imports", import.span);
      if (!loadImports(*selected))
        return false;
      height[id] = std::max(height[id], height[target] + 1);
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
        auto found = visible[target].find(name);
        if (found == visible[target].end())
          return types.fail("source.import", "unknown import: " + name,
                            import.span);
        if (!bind(name, found->second.target))
          return false;
      }
      if (import.alias && !bind(*import.alias, *selected))
        return false;
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
            binding.notation && binding.notation->position ==
                                    NotationDescriptor::Position::Reduction;
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
    }
    for (auto *sites : {&visibleOperators[id], &exportedOperators[id]}) {
      llvm::sort(*sites);
      sites->erase(std::unique(sites->begin(), sites->end()), sites->end());
    }
    --depth;
    state[id] = 2;
    return true;
  };
  for (auto id : moduleIds)
    if (!loadImports(id))
      return false;
  loadImports = {};
  if (!moduleContracts())
    return false;
  checkingVisibility = true;
  for (auto id : moduleIds) {
    const auto &context = output.declarations[id.index];
    for (const auto &import : sources[id.index]->imports) {
      auto target = resolve(context, import.module, import.span);
      if (!target)
        return false;
      auto exportable = [&](DeclarationId declaration) {
        return !import.isPublic ||
               output.declarations[declaration.index].isPublic ||
               types.fail(
                   "source.private",
                   "a public import cannot publish a private declaration",
                   import.span, {output.declarations[declaration.index].span});
      };
      if (import.alias && !exportable(*target))
        return false;
      for (const auto &name : import.names) {
        auto selected = member(context, *target, name, import.span);
        if (!selected || !exportable(*selected))
          return false;
      }
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
