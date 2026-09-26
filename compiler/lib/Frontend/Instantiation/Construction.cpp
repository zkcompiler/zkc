#include "../Model/Checked.h"
#include "../Resolution/Project.h"
#include "zkc/Frontend/Compile.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::frontend {
Expected<source::Construction>
bindConstruction(const CheckedModule &checked,
                 source::Construction descriptor) {
  if (descriptor.draws.size() > 32768)
    return zkc::error("construction-descriptor-limit");
  const auto &model = checked.completed->model;
  const auto *sourceModule =
      std::get_if<source::Module>(&checked.completed->content);
  if (!sourceModule)
    return zkc::error("construction-input-kind");
  const auto &source = *sourceModule;
  assert(model.resolution && "checked source retains resolved project input");
  if (model.resolution->carrier)
    return descriptor;
  const auto &context = *model.resolution;
  auto indexed = resolution::constructionSelectors(context);
  if (!indexed)
    return indexed.takeError();
  const auto &index = *indexed;
  std::set<std::string> functions;
  std::map<std::string, std::string> functionOrigins;
  std::set<std::string> sharedOrigins, authoredGroups, ambiguousFunctions;
  // A function declared under this name, as opposed to the copies and entries
  // that linking and imports emit under an existing origin.
  auto authored = [&](const std::string &name) {
    auto found = index.selectors.find(name);
    if (found == index.selectors.end())
      return false;
    const auto &d = context.declarations[found->second];
    return d.kind == resolution::Declaration::Kind::Function &&
           d.symbol == name;
  };
  for (const auto &function : source.functions) {
    functions.insert(function.name);
    if (function.origin) {
      functionOrigins.emplace(function.name, function.origin->definition);
      if (function.origin->definition != function.name) {
        sharedOrigins.insert(function.origin->definition);
        if (authored(function.name))
          authoredGroups.insert(function.origin->definition);
      }
    }
  }
  // A function whose name is also an origin other functions share names two
  // selections: the function alone, and that group. Its own copies share the
  // origin as expanded copies do; another declared function sharing it makes a
  // group the function belongs to, which its selector would also reach.
  for (const auto &[name, logical] : functionOrigins)
    if (sharedOrigins.count(name) &&
        (name != logical || authoredGroups.count(name)))
      ambiguousFunctions.insert(name);
  auto bind = [&](std::string &name, bool origin) -> Error {
    if (!origin) {
      auto entry = index.entrySelectors.find(name);
      if (entry != index.entrySelectors.end()) {
        name = context.declarations[entry->second].symbol;
        return Error::success();
      }
    }
    auto head = name;
    std::string suffix;
    for (;;) {
      if (index.ambiguousOrigins.count(head))
        return zkc::error("construction-source-selector-ambiguous");
      auto found = index.selectors.find(head);
      if (found != index.selectors.end()) {
        const auto &d = context.declarations[found->second];
        // A definition selector follows all its instantiations; a configure
        // selector names one closed instance. Ordinary functions are direct
        // selectors, including explicit group members. Generic functions are
        // emitted as definitions under their origins.
        const bool direct =
            d.kind == resolution::Declaration::Kind::Configuration ||
            (d.kind == resolution::Declaration::Kind::Function &&
             functions.count(d.symbol));
        // An imported function's emitted entry can hold no primitive: its body
        // is a copy made where it is linked, and every such copy shares the
        // origin allocated to its declaration, which nothing else claims. Its
        // selector binds to that origin to reach them. An application-root
        // function keeps its own symbol, which group siblings do not share.
        const bool imported =
            d.kind == resolution::Declaration::Kind::Function &&
            !authored(d.symbol);
        name = (origin && (!direct || imported) ? d.origin : d.symbol) + suffix;
        // A logical name other declared functions share is valid source, but
        // this two-field carrier selector cannot encode just the direct
        // declaration.
        if (origin && direct && ambiguousFunctions.count(name))
          return zkc::error("construction-source-selector-ambiguous");
        return Error::success();
      }
      auto dot = head.rfind('.');
      if (dot == std::string::npos)
        return Error::success(); // An exact closed selector is admitted
                                 // downstream.
      suffix = head.substr(dot) + suffix;
      head.resize(dot);
    }
  };
  if (auto e = bind(descriptor.entry, false))
    return std::move(e);
  for (auto &draw : descriptor.draws)
    if (auto e = bind(draw.first, true))
      return std::move(e);
  // Construction selects every copy a selector reaches, and normalized site
  // resolution renames a selector's site through its declaration's site map
  // (docs/spec/profiles/compiler/local-algorithms.md): a generic definition's
  // map is shared by its instantiations, a function's is its own. An explicit
  // origin group names no declaration and has no site map, so under normalized
  // identity its selector is written out as the functions carrying the site,
  // each then resolved through its own map.
  if (descriptor.identity != source::Construction::Identity::Normalized)
    return descriptor;
  using Key = std::pair<std::string, std::string>;
  std::set<std::string> declared;
  for (const auto &function : source.functions)
    declared.insert(function.name);
  for (const auto &definition : source.definitions)
    declared.insert(definition.name);
  for (const auto &configuration : source.configurations)
    declared.insert(configuration.name);
  // Index actual occurrences, not every function in a group, so a member
  // without the site is not selected.
  std::map<Key, std::vector<std::string>> occurrences;
  size_t work = 0;
  for (const auto &function : source.functions) {
    if (!function.body || !function.origin ||
        function.origin->definition == function.name)
      continue;
    source::walk(*function.body, [&](const source::Instruction &instruction) {
      if (++work > 1000000 || instruction.site.empty())
        return;
      occurrences[{function.origin->definition, instruction.site}].push_back(
          function.name);
    });
    if (work > 1000000)
      return zkc::error("construction-analysis-limit");
  }
  // Naming one selector twice is malformed. Check the bound selectors before
  // writing any out, so that writing out cannot hide a repeat.
  if (std::set<Key>(descriptor.draws.begin(), descriptor.draws.end()).size() !=
      descriptor.draws.size())
    return zkc::error("construction-draw-selector");
  auto draws = std::move(descriptor.draws);
  descriptor.draws.clear();
  std::set<Key> written;
  for (const auto &draw : draws) {
    auto found =
        declared.count(draw.first) ? occurrences.end() : occurrences.find(draw);
    // A selector with no occurrence is kept; normalized site resolution
    // diagnoses it with source-site-selection before construction.
    const std::vector<std::string> own{draw.first};
    for (const auto &function :
         found == occurrences.end() ? own : found->second) {
      if (found != occurrences.end() && ambiguousFunctions.count(function))
        return zkc::error("construction-source-selector-ambiguous");
      if (!written.insert({function, draw.second}).second)
        continue;
      if (descriptor.draws.size() == 32768)
        return zkc::error("construction-descriptor-limit");
      descriptor.draws.emplace_back(function, draw.second);
    }
  }
  return descriptor;
}
} // namespace zkc::frontend
