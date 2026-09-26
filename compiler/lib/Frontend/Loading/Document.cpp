#include "../../Support/Input.h"
#include "Requests.h"
#include "zkc/Frontend/Compile.h"
#include "zkc/Frontend/Loading.h"
#include "zkc/Support/Json.h"
#include <filesystem>
#include <map>

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
  auto input = Input::withoutFile(text.str(), filename.str());
  auto declarations = inspectDependencies(input);
  // Unlike project capture, this callback API must not perform external work
  // after any parse failure, even if the parser recovered valid imports.
  if (!declarations.complete)
    return loading::dependencyError(input, declarations);
  if (declarations.form == SourceForm::Construction)
    return parseProtocolDocument(text, filename);
  loading::RequestBudget budget;
  if (auto error = budget.preflight(declarations.relations))
    return std::move(error);
  std::vector<ProjectAsset> assets;
  for (const auto &import : declarations.relations) {
    auto maximum = budget.maximum(import);
    if (!maximum)
      return maximum.takeError();
    auto bytes = resolver(import.path, *maximum);
    if (!bytes)
      return bytes.takeError();
    if (auto error = budget.charge(bytes->size(), *maximum))
      return std::move(error);
    assets.push_back({0, import.path, std::move(*bytes)});
  }
  auto project =
      ProjectInput::capture({{{{{}, std::move(input)}}}}, std::move(assets));
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
