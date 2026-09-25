#include "zkc/Frontend/Input.h"
#include "zkc/Source/Relations.h"
#include "zkc/Support/Json.h"
#include <set>

using namespace llvm;
namespace zkc::frontend {
ProjectInput::ProjectInput(Contents c)
    : contents(std::make_shared<const Contents>(std::move(c))) {}

Expected<ProjectInput>
ProjectInput::capture(std::vector<ProjectLibrary> libraries,
                      std::vector<ProjectAsset> assets) {
  if (libraries.empty() || libraries.size() > maxLibraries)
    return zkc::error("project-library-limit");
  size_t sources = 0, bytes = 0;
  for (const auto &library : libraries) {
    std::set<std::vector<std::string>> paths;
    for (const auto &source : library.sources) {
      if (++sources > maxSources ||
          source.input.text().size() > maxSourceBytes ||
          source.input.text().size() > maxTotalSourceBytes - bytes)
        return zkc::error("project-source-limit");
      bytes += source.input.text().size();
      if (!paths.insert(source.module).second)
        return zkc::error("project-module-duplicate");
      if (source.module.size() > 64)
        return zkc::error("project-module-depth");
      for (const auto &name : source.module)
        if (name.empty() || name.size() > 128 || name == "." || name == ".." ||
            name.find_first_of("/\\\0", 0, 3) != std::string::npos)
          return zkc::error("project-module-name");
    }
    if (!paths.count({}))
      return zkc::error("project-module-root");
  }
  if (assets.size() > relation::DependencyLimits::count)
    return zkc::error("relation-dependency-limit");
  bytes = 0;
  std::set<std::pair<uint32_t, std::string>> keys;
  for (const auto &asset : assets) {
    if (asset.file >= sources || !keys.emplace(asset.file, asset.path).second)
      return zkc::error("project-asset-owner");
    if (asset.bytes.size() > relation::DependencyLimits::bytes - bytes)
      return zkc::error("relation-dependency-limit");
    bytes += asset.bytes.size();
  }
  return ProjectInput({std::move(libraries), std::move(assets)});
}
ProjectInput ProjectInput::single(Input input) {
  // A single parser still enforces its existing byte/token limits.
  return ProjectInput({{{{{{}, std::move(input)}}}}, {}});
}
ArrayRef<ProjectLibrary> ProjectInput::libraries() const {
  return contents->libraries;
}
ArrayRef<ProjectAsset> ProjectInput::assets() const { return contents->assets; }
const Input *ProjectInput::file(uint32_t id) const {
  for (const auto &library : contents->libraries)
    for (const auto &source : library.sources)
      if (id-- == 0)
        return &source.input;
  return nullptr;
}
} // namespace zkc::frontend
