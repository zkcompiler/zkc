#include "Language.h"
#include "../Support/Input.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/LanguagePackage.h"
#include "zkc/Language/Diagnostics.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
namespace zkc {
int runLanguageCompiler(int argc, char **argv) {
  using namespace language;
  std::vector<SourceBuffer> sources;
  std::vector<AssetBuffer> assets;
  std::optional<CapturedProject> captured;
  std::string entry, format;
  bool declarations = false;
  EntryOptions options;
  Limits limits;
  auto refuse = [&](Error error) {
    handleAllErrors(
        std::move(error),
        [&](const DiagnosticError &diagnostic) {
          const auto &value = diagnostic.diagnostic();
          if (captured)
            errs() << formatDiagnostics(*captured, {value});
          else {
            printEscapedString(StringRef(value.code).take_front(128), errs());
            errs() << ": ";
            printEscapedString(StringRef(value.message).take_front(2048),
                               errs());
            errs() << '\n';
          }
        },
        [&](const CompilationError &diagnostic) {
          for (const auto &refusal : diagnostic.refusals)
            errs() << refusal.code << ": " << refusal.detail << '\n';
          errs() << diagnostic.message << '\n';
          for (const auto &location : diagnostic.locations) {
            errs() << "at ";
            printEscapedString(StringRef(location.filename).take_front(512),
                               errs());
            errs() << ':' << location.line << ':' << location.column << '\n';
          }
        },
        [&](const ErrorInfoBase &diagnostic) {
          errs() << diagnostic.message() << '\n';
        });
    return 1;
  };
  StringRef command(argv[1]);
  if (command != "language-check" && command != "language-emit" &&
      command != "language-interface" && command != "language-bundle" &&
      command != "language-package")
    return refuse(error("source.command", "unknown language command"));
  if (argc > int(limits.files + 8))
    return refuse(error("source.limit", "too many source command arguments"));
  uint64_t total = 0, assetTotal = 0;
  for (int i = 2; i < argc; ++i) {
    StringRef arg(argv[i]);
    if (arg.consume_front("--source-format=")) {
      if (!format.empty())
        return refuse(error("source.options", "duplicate source format"));
      format = arg.str();
    } else if (arg.consume_front("--entry=")) {
      if (!entry.empty())
        return refuse(error("source.options", "duplicate Entry selection"));
      entry = arg.str();
    } else if (arg.consume_front("--module=")) {
      auto [name, path] = arg.split('=');
      if (name.empty() || path.empty() || path.size() > 4096 ||
          sources.size() + assets.size() == limits.files)
        return refuse(
            error("source.options", "expected --module=LOGICAL_NAME=FILE"));
      auto bytes = readInput(
          path, std::min(limits.fileBytes, limits.captureBytes - total));
      if (!bytes)
        return refuse(bytes.takeError());
      total += bytes->size();
      sources.push_back({name.str(), std::move(*bytes), path.str()});
    } else if (arg.consume_front("--asset=")) {
      auto [name, rest] = arg.split('=');
      auto [format, path] = rest.split('=');
      if (name.empty() || path.empty() || path.size() > 4096 ||
          sources.size() + assets.size() == limits.files ||
          (format != "r1cs-json" && format != "r1cs-binary" &&
           format != "air-json" && format != "ring-json" &&
           format != "relation-bundle-json"))
        return refuse(
            error("source.options", "expected --asset=NAME=FORMAT=FILE"));
      auto bytes =
          readInput(path, std::min(limits.assetBytes,
                                   limits.assetTotalBytes - assetTotal));
      if (!bytes)
        return refuse(bytes.takeError());
      assetTotal += bytes->size();
      assets.push_back(
          {name.str(), format.str(), std::move(*bytes), path.str()});
    } else if (arg == "--declarations") {
      if (declarations || command != "language-check")
        return refuse(
            error("source.options",
                  "--declarations is a check option and may appear once"));
      declarations = true;
    } else if (arg == "--no-simplify")
      options.simplify = false;
    else if (arg == "--release-storage")
      options.releaseStorage = true;
    else
      return refuse(error("source.options", "unknown language option: " + arg));
  }
  if (format.empty() || (entry.empty() && command != "language-check"))
    return refuse(error("source.options",
                        "--source-format=zkc is required; output "
                        "commands also require --entry"));
  auto captureResult = capture(std::move(sources), std::move(assets),
                               CaptureOptions{format, limits});
  if (!captureResult)
    return refuse(captureResult.takeError());
  captured = std::move(*captureResult);
  auto analysis = analyze(*captured);
  if (!analysis.diagnostics().empty()) {
    errs() << formatDiagnostics(*captured, analysis.diagnostics());
    return 1;
  }
  auto project = analysis.checkedProject();
  if (!project)
    return refuse(project.takeError());
  json::Object checked{{"format", "zkc.source-check/0"},
                       {"status", "checked"},
                       {"scope", entry.empty() ? "definitions" : "entry"},
                       {"capture", captured->identity()},
                       {"installation", project->installationIdentity()}};
  if (declarations) {
    auto report = inspectDeclarations(*project, limits);
    if (!report)
      return refuse(report.takeError());
    checked["declarations"] = cantFail(json::parse(*report));
  }
  if (entry.empty()) {
    outs() << json::Value(std::move(checked)) << '\n';
    return 0;
  }
  auto selected = closeEntry(*project, entry);
  if (!selected)
    return refuse(selected.takeError());
  auto original = prepareOriginal(*selected);
  if (!original)
    return refuse(original.takeError());
  if (command == "language-check") {
    checked["entry"] = entry;
    checked["original"] = original->identity();
    outs() << json::Value(std::move(checked)) << '\n';
    return 0;
  }
  if (command == "language-emit") {
    outs() << original->bytes();
    return 0;
  }
  if (command == "language-interface") {
    outs() << original->interfaceJson() << '\n';
    return 0;
  }
  auto compiled = compileEntry(*original, options);
  if (!compiled)
    return refuse(compiled.takeError());
  if (command == "language-package") {
    auto package = packageEntry(*compiled);
    if (!package)
      return refuse(package.takeError());
    outs() << package->bytes();
    return 0;
  }
  outs() << compiled->bytes() << '\n';
  return 0;
}
} // namespace zkc
