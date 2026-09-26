#include "../../Support/Input.h"
#include "Requests.h"
#include "zkc/Frontend/Loading.h"
#include "zkc/Support/Json.h"
#include <algorithm>
#include <filesystem>
#include <map>
#include <set>

using namespace llvm;
namespace zkc::frontend {
namespace {
namespace fs = std::filesystem;

struct Capture {
  // Cache physical reads project-wide, including explicitly supplied roots.
  // Limits also count each owned logical source/asset, even if bytes are
  // shared.
  std::map<fs::path, std::string> bytes;
  std::vector<ProjectLibrary> libraries;
  std::vector<ProjectAsset> assets;
  size_t sourceCount = 0, sourceBytes = 0;
  loading::RequestBudget assetBudget;

  Expected<fs::path> regular(const fs::path &path, const fs::path &base,
                             bool asset) {
    std::error_code ec;
    auto resolved = fs::canonical(path, ec);
    if (ec)
      return zkc::error(asset ? "relation-asset-missing"
                              : "project-source-missing");
    if (!base.empty() && !loading::contained(base, resolved))
      return zkc::error(asset ? "relation-asset-path" : "project-source-path");
    if (!fs::is_regular_file(resolved, ec) || ec)
      return zkc::error(asset ? "relation-asset-missing"
                              : "project-source-missing");
    return resolved;
  }

  Expected<StringRef> read(const fs::path &path, size_t maximum) {
    auto found = bytes.find(path);
    if (found == bytes.end()) {
      auto input = zkc::readInput(path.string(), maximum);
      if (!input)
        return input.takeError();
      found = bytes.emplace(path, std::move(*input)).first;
    }
    if (found->second.size() > maximum)
      return zkc::error("byte-limit");
    return StringRef(found->second);
  }

  Error source(ProjectLibrary &library, const fs::path &base,
               const fs::path &physical, std::vector<std::string> logical,
               Input input, std::set<fs::path> &ancestors) {
    if (logical.size() > 64)
      return zkc::error("project-module-depth");
    if (sourceCount == ProjectInput::maxSources ||
        input.text().size() > ProjectInput::maxSourceBytes ||
        input.text().size() > ProjectInput::maxTotalSourceBytes - sourceBytes)
      return zkc::error("project-source-limit");
    if (!ancestors.insert(physical).second)
      return zkc::error("project-module-cycle");
    uint32_t file = sourceCount++;
    sourceBytes += input.text().size();
    library.sources.push_back({logical, input});

    // Retain incomplete spelling for the pure analyzer's recovery diagnostics.
    // Any recovered declarations are still parsed syntax, never text scanning.
    auto declarations = inspectDependencies(input, file);
    if (!declarations.recoverable)
      return loading::dependencyError(input, declarations);
    if (declarations.form == SourceForm::Construction) {
      if (!logical.empty())
        return zkc::error("project-module-root");
      ancestors.erase(physical);
      return Error::success();
    }
    if (!logical.empty() && (!declarations.libraryIdentities.empty() ||
                             !declarations.libraries.empty()))
      return zkc::error("project-library-root");

    if (auto error = assetBudget.preflight(declarations.relations))
      return error;
    std::set<std::string> paths;
    for (const auto &import : declarations.relations) {
      auto maximum = assetBudget.maximum(import, "byte-limit");
      if (!maximum)
        return maximum.takeError();
      auto path = regular(physical.parent_path() / import.path, base, true);
      if (!path)
        return path.takeError();
      // Each (file, reference) is stored once. Charge every import against the
      // total decoding budget, as the callback loader does for several aliases.
      bool first = paths.insert(import.path).second;
      auto content = read(*path, *maximum);
      if (!content)
        return content.takeError();
      if (auto error = assetBudget.charge(content->size(), *maximum))
        return error;
      if (first)
        assets.push_back({file, import.path, content->str()});
    }

    for (const auto &child : declarations.modules) {
      auto childLogical = logical;
      childLogical.push_back(child.name);
      if (childLogical.size() > 64)
        return zkc::error("project-module-depth");
      if (sourceCount == ProjectInput::maxSources)
        return zkc::error("project-source-limit");
      auto childPath = base;
      for (const auto &part : childLogical)
        childPath /= part;
      childPath += ".pir";
      auto path = regular(childPath, base, false);
      if (!path)
        return path.takeError();
      auto content = read(
          *path, std::min(ProjectInput::maxSourceBytes,
                          ProjectInput::maxTotalSourceBytes - sourceBytes));
      if (!content)
        return content.takeError();
      if (auto error = source(library, base, *path, std::move(childLogical),
                              Input(content->str(), path->string()), ancestors))
        return error;
    }
    ancestors.erase(physical);
    return Error::success();
  }
};
} // namespace

Expected<ProjectInput> captureProject(Input application,
                                      ArrayRef<Input> libraryRoots) {
  if (libraryRoots.size() >= ProjectInput::maxLibraries)
    return zkc::error("project-library-limit");
  Capture capture;
  std::vector<Input> roots{std::move(application)};
  roots.insert(roots.end(), libraryRoots.begin(), libraryRoots.end());
  std::vector<fs::path> paths;
  size_t rootBytes = 0;
  // Seed all explicit snapshots before following any child path, so an
  // explicitly supplied file is never silently reopened with different bytes.
  for (const auto &root : roots) {
    // Child modules and assets are found relative to the root's file.
    if (!root.file() || root.filename().empty())
      return zkc::error("project-source-base");
    if (root.text().size() > ProjectInput::maxSourceBytes ||
        root.text().size() > ProjectInput::maxTotalSourceBytes - rootBytes)
      return zkc::error("project-source-limit");
    rootBytes += root.text().size();
    auto path = capture.regular(fs::path(root.filename().str()), {}, false);
    if (!path)
      return path.takeError();
    auto [existing, inserted] = capture.bytes.emplace(*path, root.text().str());
    if (!inserted && existing->second != root.text())
      return zkc::error("project-source-conflict");
    paths.push_back(std::move(*path));
  }
  for (size_t index = 0; index < roots.size(); ++index) {
    ProjectLibrary library;
    std::set<fs::path> ancestors;
    if (auto error = capture.source(library, paths[index].parent_path(),
                                    paths[index], {}, roots[index], ancestors))
      return std::move(error);
    capture.libraries.push_back(std::move(library));
  }
  return ProjectInput::capture(std::move(capture.libraries),
                               std::move(capture.assets));
}
} // namespace zkc::frontend
