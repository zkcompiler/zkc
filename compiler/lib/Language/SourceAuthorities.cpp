#include "State.h"
#include "llvm/ADT/STLExtras.h"
#include <set>

using namespace llvm;
namespace zkc::language {
namespace detail {
namespace {
constexpr StringLiteral authorityFormat = "zkc.language.authority/0";
} // namespace

Error computeSourceAuthorities(CheckedStorage &storage,
                               const std::map<uint32_t, unsigned> &assetDomains,
                               Work &work) {
  const auto &sources = *storage.sources;
  const auto &declarations = storage.declarations;
  const auto &references = storage.api.references;
  auto captured = storage.capture.assets();
  SourceAuthorities table;
  table.sources.resize(sources.size());
  if (auto error = work.charge(sources.size() + declarations.size() +
                               references.size() + assetDomains.size() + 1))
    return error;
  std::vector<unsigned> order;
  for (unsigned i = 0; i < sources.size(); ++i)
    if (sources[i].origin == SourceOrigin::Captured)
      order.push_back(i);
  llvm::sort(order, [&](unsigned left, unsigned right) {
    return sources[left].module < sources[right].module;
  });
  for (auto source : order) {
    table.sources[source] = table.units.size();
    table.units.push_back({sources[source].module, SourceId{source}, {}, {}});
  }
  const auto count = table.units.size();
  // A generated declaration belongs to its family target's unit; an installed
  // declaration belongs to none.
  auto unit = [&](DeclarationId id) -> std::optional<unsigned> {
    const auto *decl = &declarations[id.index];
    if (decl->generated)
      decl = &declarations[decl->generated->target.index];
    return table.sources[decl->span.source.index];
  };
  std::vector<std::set<unsigned>> dependencies(count);
  auto depend = [&](std::optional<unsigned> from, std::optional<unsigned> to) {
    if (from && to && *from != *to)
      dependencies[*from].insert(*to);
  };
  // A linked child file and its parent share representation authority.
  for (const auto &decl : declarations)
    if (decl.kind == Declaration::Kind::Module && decl.parent) {
      auto child = unit(decl.id), parent = unit(*decl.parent);
      depend(child, parent);
      depend(parent, child);
    }
  // Every recorded route of a declaration defined in a unit adds the units of
  // its provider and target. An abstract reference adds only the interface
  // member's unit, never a module that a closed instance later substitutes.
  for (const auto &reference : references) {
    auto owner = unit(reference.owner);
    if (!reference.abstractModule)
      depend(owner, unit(reference.provider));
    depend(owner, unit(reference.target));
  }
  std::vector<std::set<unsigned>> assets(count);
  for (auto [declaration, asset] : assetDomains)
    if (auto at = unit(DeclarationId{declaration}))
      assets[*at].insert(asset);
  for (const auto &decl : declarations)
    if (decl.relation && decl.relation->asset)
      if (auto at = unit(decl.id))
        assets[*at].insert(*decl.relation->asset);
  std::vector<std::string> unitDigests, assetDigests;
  for (const auto &entry : table.units) {
    const auto &text = sources[entry.source.index].text;
    if (auto error = work.charge(text.size() + 1))
      return error;
    unitDigests.push_back(digest(text));
  }
  for (const auto &asset : captured) {
    if (auto error = work.charge(asset.bytes.size() + 1))
      return error;
    assetDigests.push_back(digest(asset.bytes));
  }
  for (unsigned u = 0; u < count; ++u) {
    std::vector<bool> member(count);
    std::vector<unsigned> pending{u};
    member[u] = true;
    while (!pending.empty()) {
      auto at = pending.back();
      pending.pop_back();
      if (auto error = work.charge(dependencies[at].size() + 1))
        return error;
      for (auto next : dependencies[at])
        if (!member[next]) {
          member[next] = true;
          pending.push_back(next);
        }
    }
    // Units are sorted by module path, so index order is path order.
    std::vector<unsigned> closure;
    std::vector<std::pair<unsigned, unsigned>> edges;
    std::set<unsigned> named;
    for (unsigned at = 0; at < count; ++at) {
      if (!member[at])
        continue;
      closure.push_back(at);
      for (auto next : dependencies[at])
        edges.emplace_back(at, next);
      named.insert(assets[at].begin(), assets[at].end());
    }
    std::vector<unsigned> assetOrder(named.begin(), named.end());
    llvm::sort(assetOrder, [&](unsigned left, unsigned right) {
      return captured[left].name < captured[right].name;
    });
    std::string preimage;
    frame(preimage, authorityFormat);
    frame(preimage, storage.capture.format());
    frame(preimage, storage.installation);
    frame(preimage, table.units[u].module);
    frame(preimage, std::to_string(closure.size()));
    for (auto at : closure) {
      frame(preimage, table.units[at].module);
      frame(preimage,
            std::to_string(sources[table.units[at].source.index].text.size()));
      frame(preimage, unitDigests[at]);
    }
    frame(preimage, std::to_string(edges.size()));
    for (auto [from, to] : edges) {
      frame(preimage, table.units[from].module);
      frame(preimage, table.units[to].module);
    }
    frame(preimage, std::to_string(assetOrder.size()));
    for (auto asset : assetOrder) {
      frame(preimage, captured[asset].name);
      frame(preimage, captured[asset].format);
      frame(preimage, assetDigests[asset]);
    }
    if (auto error = work.charge(preimage.size() + 1))
      return error;
    table.units[u].revision = digest(preimage);
    table.units[u].dependencies.assign(dependencies[u].begin(),
                                       dependencies[u].end());
  }
  table.computed = true;
  storage.authorities = std::move(table);
  return Error::success();
}

Expected<std::optional<std::string>>
definingAuthority(const CheckedStorage &storage, StringRef path) {
  auto id = storage.declarationIndex ? storage.declarationIndex->canonical(path)
                                     : std::nullopt;
  if (!id)
    return failure("source.authority",
                   "no checked declaration has path " + path);
  const auto &decl = storage.declarations[id->index];
  // A generated declaration's family identity already binds the capture and
  // installation; it never receives an authored revision.
  if (decl.generated)
    return std::optional<std::string>{};
  const auto source = decl.span.source.index;
  if ((*storage.sources)[source].origin == SourceOrigin::Installation)
    return std::optional<std::string>(storage.installation);
  const auto &table = storage.authorities;
  if (!table.computed || source >= table.sources.size() ||
      !table.sources[source])
    return failure("source.authority",
                   "authored declaration has no source authority: " + path,
                   decl.span);
  return std::optional<std::string>(
      table.units[*table.sources[source]].revision);
}
} // namespace detail

Expected<std::optional<std::string>>
sourceAuthority(const CheckedProject &project, StringRef path) {
  return detail::definingAuthority(*project.storage, path);
}
} // namespace zkc::language
