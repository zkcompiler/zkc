#include "../Support/Input.h"
#include "Syntax/Tree.h"
#include "zkc/Frontend/Dependencies.h"
#include "zkc/Target/Json.h"
#include <algorithm>
#include <filesystem>
#include <map>
#include <set>

using namespace llvm;
namespace zkc::frontend {
namespace {
namespace fs = std::filesystem;

bool contained(const fs::path &base, const fs::path &path) {
  return std::mismatch(base.begin(), base.end(), path.begin(), path.end())
             .first == base.end();
}
bool relativeAsset(StringRef name) {
  if (name.empty() || name.size() > 4096 || name.contains('\\') ||
      name.contains('\0'))
    return false;
  fs::path path(name.str());
  if (path.is_absolute())
    return false;
  for (const auto &part : path)
    if (part == "..")
      return false;
  return true;
}
bool moduleName(StringRef name) {
  return !name.empty() && name.size() <= 128 && name != "." && name != ".." &&
         !name.contains('/') && !name.contains('\\') && !name.contains('\0');
}

struct Capture {
  // Cache physical reads project-wide, including explicitly supplied roots.
  // Limits also count each owned logical source/asset, even if bytes are
  // shared.
  std::map<fs::path, std::string> bytes;
  std::vector<ProjectLibrary> libraries;
  std::vector<ProjectAsset> assets;
  size_t sourceCount = 0, sourceBytes = 0, assetCount = 0, assetBytes = 0;

  Expected<fs::path> regular(const fs::path &path, const fs::path &base,
                             bool asset) {
    std::error_code ec;
    auto resolved = fs::canonical(path, ec);
    if (ec)
      return zkc::error(asset ? "relation-asset-missing"
                              : "project-source-missing");
    if (!base.empty() && !contained(base, resolved))
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
    auto parsed =
        syntax::parseRecoverable(input.text(), input.filename(), file);
    if (!parsed.content) {
      auto failed = syntax::parse(input.text(), input.filename(), file);
      if (!failed)
        return failed.takeError();
      return zkc::error("source-syntax");
    }
    auto *module = std::get_if<syntax::Module>(&*parsed.content);
    if (!module) {
      if (!logical.empty())
        return zkc::error("project-module-root");
      ancestors.erase(physical);
      return Error::success();
    }
    if (!logical.empty() &&
        (!module->libraryIdentities.empty() || !module->dependencies.empty()))
      return zkc::error("project-library-root");

    if (module->imports.size() > relation::DependencyLimits::count - assetCount)
      return zkc::error("relation-dependency-limit");
    assetCount += module->imports.size();
    std::set<std::string> names;
    for (const auto &import : module->imports) {
      if (!names.insert(import.name).second)
        return zkc::error("relation-duplicate-alias");
      if (import.family != "r1cs" && import.family != "air")
        return zkc::error("relation-import-family");
      if (!relativeAsset(import.path))
        return zkc::error("relation-asset-path");
    }
    std::set<std::string> children;
    for (const auto &child : module->modules) {
      if (!moduleName(child.name))
        return zkc::error("project-module-name");
      if (!children.insert(child.name).second)
        return zkc::error("project-module-duplicate");
    }
    std::set<std::string> paths;
    for (const auto &import : module->imports) {
      auto path = regular(physical.parent_path() / import.path, base, true);
      if (!path)
        return path.takeError();
      const auto familyMaximum = import.family == "air"
                                     ? relation::AIRLimits::bytes
                                     : relation::Limits::bytes;
      // Each (file, reference) is stored once. Charge every import against the
      // total decoding budget, as the callback loader does for several aliases.
      bool first = paths.insert(import.path).second;
      size_t maximum = std::min(familyMaximum,
                                relation::DependencyLimits::bytes - assetBytes);
      auto content = read(*path, maximum);
      if (!content)
        return content.takeError();
      assetBytes += content->size();
      if (first)
        assets.push_back({file, import.path, content->str()});
    }

    for (const auto &child : module->modules) {
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
