#include "zkc/Source/Resolution.h"
#include "zkc/Compiler/Instantiation.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Relation/Authoring.h"
#include "zkc/Source/Codec.h"
#include "zkc/Target/Json.h"
#include <set>

using namespace llvm;
namespace zkc::source {
namespace {
using Targets = std::map<std::string, std::string>;
using Sites = std::map<std::pair<std::string, std::string>, std::string>;

// Called only on admitted bodies. Sites are declaration-wide, including nested
// loops. Rename each actual node once; do not replace arbitrary strings.
void resolveBody(Body &body, StringRef owner, Sites &sites) {
  size_t next = 0;
  walk(body, [&](Instruction &instruction) {
    if (instruction.get<Return>() || instruction.get<Yield>())
      return;
    auto site = "site" + std::to_string(next++);
    sites.emplace(std::make_pair(owner.str(), instruction.site), site);
    instruction.site = std::move(site);
  });
}

Expected<std::string> definitionOf(StringRef name, const Targets &targets,
                                   const std::set<std::string> &definitions) {
  std::set<std::string> visited;
  auto current = name.str();
  while (!definitions.count(current)) {
    auto found = targets.find(current);
    if (found == targets.end() || !visited.insert(current).second)
      return error("source-site-target");
    current = found->second;
  }
  return current;
}
} // namespace

Expected<SiteResolution> resolveProtocolSites(const Module &value) {
  if (auto e = checkStructure(value))
    return e;
  if (value.isLibrary()) {
    auto admitted = generic::prepareLibrary(value);
    if (!admitted)
      return admitted.takeError();
  } else if (auto e = protocol::admit(value, false)) {
    return e;
  }
  SiteResolution result{value, {}, {}, {}, {}};
  auto generated = relation::associations(value);
  if (!generated)
    return generated.takeError();
  for (auto &function : result.source.functions)
    if (function.body && !generated->count(function.name))
      resolveBody(*function.body, function.name, result.functions);
  for (auto &protocol : result.source.protocols)
    if (protocol.body)
      resolveBody(*protocol.body, protocol.name, result.protocols);
  if (!value.isLibrary())
    return result;

  std::set<std::string> definitions;
  for (auto &definition : result.source.definitions) {
    definitions.insert(definition.name);
    resolveBody(definition.body, definition.name, result.definitions);
  }
  Targets targets;
  for (const auto &configuration : result.source.configurations)
    targets.emplace(configuration.name, configuration.base);
  for (auto &configuration : result.source.configurations) {
    auto definition = definitionOf(configuration.name, targets, definitions);
    if (!definition)
      return definition.takeError();
    // One alias edge also covers unused configurations without multiplying
    // the site map by the number of configurations.
    result.configurations.emplace(configuration.name, *definition);
    for (auto &[site, implementation] : configuration.implementations) {
      auto found = result.definitions.find({*definition, site});
      if (found == result.definitions.end())
        return error("source-site-selection");
      site = found->second;
    }
  }
  return result;
}

Expected<Construction>
SiteResolution::descriptor(const Construction &value) const {
  if (auto e = checkStructure(value))
    return e;
  if (value.identity != Construction::Identity::Normalized)
    return error("construction-descriptor");
  // A selector matches both concrete names and logical origins. They may
  // legitimately overlap (e.g. ordinary helper specializations), and each
  // body numbers its sites independently. Check both directions so replacing
  // a raw label neither loses a selected occurrence nor selects another one.
  // An empty index value marks conflicting coordinates, not invalid source.
  Sites forward, reverse;
  auto record = [](Sites &index, const auto &key, const std::string &target) {
    auto [it, inserted] = index.emplace(key, target);
    if (!inserted && it->second != target)
      it->second.clear();
  };
  Targets origins;
  for (const auto &function : source.functions)
    if (function.origin)
      origins.emplace(function.name, function.origin->definition);
  for (const auto &[key, coordinate] : functions) {
    record(forward, key, coordinate);
    record(reverse, std::make_pair(key.first, coordinate), key.second);
    if (auto origin = origins.find(key.first); origin != origins.end()) {
      record(forward, std::make_pair(origin->second, key.second), coordinate);
      record(reverse, std::make_pair(origin->second, coordinate), key.second);
    }
  }
  Construction result = value;
  for (auto &[owner, site] : result.draws) {
    auto configuration = configurations.find(owner);
    const auto &sites = configuration == configurations.end() &&
                                !definitions.count({owner, site})
                            ? functions
                            : definitions;
    const auto &name =
        configuration == configurations.end() ? owner : configuration->second;
    auto found = sites.find({name, site});
    if (found == sites.end())
      return error("source-site-selection");
    auto actual = forward.find({owner, site});
    auto numbered = reverse.find({owner, found->second});
    if ((actual != forward.end() && actual->second != found->second) ||
        (numbered != reverse.end() && numbered->second != site))
      return error("construction-selector-coordinates");
    site = found->second;
  }
  return result;
}

} // namespace zkc::source
