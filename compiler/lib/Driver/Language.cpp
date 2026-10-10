#include "Language.h"
#include "../Support/Input.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/LanguagePackage.h"
#include "zkc/Language/Diagnostics.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Support/Refusal.h"
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
  std::optional<EntryKind> entryKind;
  bool declarations = false;
  EntryOptions options;
  Limits limits;
  auto refuse = [&](Error failure) {
    std::vector<Diagnostic> messages;
    auto append = [&](StringRef code, StringRef message) {
      messages.push_back(
          {code.take_front(129).str(), message.take_front(2049).str(), {}, {}});
    };
    auto appendLines = [&](StringRef message) {
      for (unsigned i = 0; i < 16 && !message.empty(); ++i) {
        auto [line, rest] = message.split('\n');
        append("", line);
        message = rest;
      }
      if (!message.empty())
        append("", "further diagnostic lines omitted");
    };
    handleAllErrors(
        std::move(failure),
        [&](const DiagnosticError &error) {
          messages.push_back(error.diagnostic());
        },
        [&](const CompilationError &error) {
          for (const auto &refusal : ArrayRef(error.refusals).take_front(16))
            append(refusal.code, refusal.detail);
          appendLines(error.message);
          for (const auto &location : ArrayRef(error.locations).take_front(4))
            append("", "at " + location.filename + ":" +
                           std::to_string(location.line) + ":" +
                           std::to_string(location.column));
        },
        [&](const ErrorInfoBase &error) { appendLines(error.message()); });
    errs() << formatDiagnostics(messages, captured ? &*captured : nullptr);
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
      if (arg.empty() || !format.empty())
        return refuse(error("source.options",
                            "source format must be nonempty and unique"));
      format = arg.str();
    } else if (arg.consume_front("--entry=")) {
      if (arg.empty() || !entry.empty())
        return refuse(error("source.options",
                            "Entry selection must be nonempty and unique"));
      entry = arg.str();
    } else if (arg.consume_front("--entry-kind=")) {
      if (entryKind || (arg != "run" && arg != "proof") ||
          command == "language-check")
        return refuse(
            error("source.options",
                  "expected one --entry-kind=run|proof for Entry compilation"));
      entryKind = arg == "run" ? EntryKind::Run : EntryKind::Proof;
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
    } else if (command == "language-check" &&
               (arg == "--no-simplify" || arg == "--release-storage"))
      return refuse(
          error("source.options",
                "checking accepts no executable optimization options"));
    else if (arg == "--no-simplify")
      options.simplify = false;
    else if (arg == "--release-storage")
      options.releaseStorage = true;
    else
      return refuse(error("source.options", "unknown language option: " + arg));
  }
  if (format.empty())
    return refuse(error("source.options", "--source-format=zkc is required"));
  auto captureResult = capture(std::move(sources), std::move(assets),
                               CaptureOptions{format, limits});
  if (!captureResult)
    return refuse(captureResult.takeError());
  captured = std::move(*captureResult);
  auto analysis = analyze(*captured);
  if (!analysis.diagnostics().empty()) {
    errs() << formatDiagnostics(analysis.diagnostics(), &*captured);
    return 1;
  }
  auto project = analysis.checkedProject();
  if (!project)
    return refuse(project.takeError());
  json::Object checked{{"format", "zkc.source-check/0"},
                       {"status", "checked"},
                       {"phase", "complete"},
                       {"scope", entry.empty() ? "definitions" : "entry"},
                       {"capture", captured->identity()},
                       {"installation", project->installationIdentity()}};
  if (command == "language-check") {
    auto inventory = inspectEntries(*project, limits);
    if (!inventory)
      return refuse(inventory.takeError());
    checked["entries"] = cantFail(json::parse(*inventory));
  }
  if (declarations) {
    auto report = inspectDeclarations(*project, limits);
    if (!report)
      return refuse(report.takeError());
    checked["declarations"] = cantFail(json::parse(*report));
  }
  if (entry.empty() && command == "language-check") {
    outs() << json::Value(std::move(checked)) << '\n';
    return 0;
  }
  auto selected = closeEntry(*project, entry, limits, entryKind);
  if (!selected)
    return refuse(selected.takeError());
  auto original = prepareOriginal(*selected);
  if (!original)
    return refuse(original.takeError());
  if (command == "language-check") {
    checked["entry"] = selected->entry().qualifiedName;
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
