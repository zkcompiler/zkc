#include "../../Support/Input.h"
#include "../Syntax/Lexer.h"
#include "../Syntax/Tree.h"
#include "Paths.h"
#include "zkc/Frontend/Compile.h"
#include "zkc/Frontend/Loading.h"
#include "zkc/Support/Json.h"
#include <filesystem>
#include <map>
#include <set>

using namespace llvm;
namespace zkc::frontend {
Expected<source::Document> loadProtocolDocument(StringRef text,
                                                StringRef filename,
                                                AssetResolver resolver) {
  if (text.ltrim().starts_with("[")) {
    auto document = parseProtocolDocument(text, filename);
    if (!document)
      return document.takeError();
    if (auto e = checkProtocolDocument(*document))
      return std::move(e);
    return std::move(*document);
  }
  auto parsed = syntax::parse(text, filename);
  if (!parsed)
    return parsed.takeError();
  auto *module = std::get_if<syntax::Module>(&*parsed);
  if (!module)
    return parseProtocolDocument(text, filename);
  if (module->imports.size() > relation::DependencyLimits::count)
    return zkc::error("relation-dependency-limit");
  std::set<std::string> names;
  for (const auto &import : module->imports) {
    if (!names.insert(import.name).second)
      return zkc::error("relation-duplicate-alias");
    if (import.family != "r1cs" && import.family != "air")
      return zkc::error("relation-import-family");
    if (!loading::relativeAsset(import.path))
      return zkc::error("relation-asset-path");
  }
  size_t total = 0;
  std::vector<ProjectAsset> assets;
  for (const auto &import : module->imports) {
    auto maximum = import.family == "air" ? relation::AIRLimits::bytes
                                          : relation::Limits::bytes;
    maximum = std::min(maximum, relation::DependencyLimits::bytes - total);
    auto bytes = resolver(import.path, maximum);
    if (!bytes)
      return bytes.takeError();
    if (bytes->size() > maximum)
      return zkc::error("relation-dependency-limit");
    total += bytes->size();
    assets.push_back({0, import.path, std::move(*bytes)});
  }
  auto project = ProjectInput::capture(
      {{{{{}, Input(text.str(), filename.str())}}}}, std::move(assets));
  if (!project)
    return project.takeError();
  auto elaborated = compileProject(*project);
  if (!elaborated)
    return elaborated.takeError();
  source::Document document(std::move(*elaborated), text.str(), filename.str());
  if (auto e = checkProtocolDocument(document))
    return std::move(e);
  return document;
}
Expected<source::Document> loadProtocolFile(const Input &source) {
  namespace fs = std::filesystem;
  StringRef text = source.text(), filename = source.filename();
  if (!source.file() || filename.empty())
    return zkc::error("relation-asset-base");
  std::error_code error;
  auto absolute = fs::absolute(fs::path(filename.str()), error);
  if (error)
    return zkc::error("relation-asset-base");
  auto base = fs::canonical(absolute.parent_path(), error);
  if (error)
    return zkc::error("relation-asset-base");
  std::map<fs::path, std::string> captured;
  return loadProtocolDocument(
      text, filename,
      [&](StringRef name, size_t maximum) -> Expected<std::string> {
        if (!loading::relativeAsset(name))
          return zkc::error("relation-asset-path");
        auto path = fs::canonical(base / name.str(), error);
        if (error || !fs::is_regular_file(path, error) || error)
          return zkc::error("relation-asset-missing");
        if (!loading::contained(base, path))
          return zkc::error("relation-asset-path");
        auto found = captured.find(path);
        if (found == captured.end()) {
          auto bytes = zkc::readInput(path.string(), maximum);
          if (!bytes)
            return bytes.takeError();
          found = captured.emplace(path, std::move(*bytes)).first;
        }
        if (found->second.size() > maximum)
          return zkc::error("byte-limit");
        return found->second;
      });
}
} // namespace zkc::frontend
