#include "Language.h"
#include "../Support/Input.h"
#include "CpuTarget.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/LanguagePackage.h"
#include "zkc/Compiler/Observation.h"
#include "zkc/Compiler/SourceClaims.h"
#include "zkc/Compiler/SourceCorrespondence.h"
#include "zkc/Language/Diagnostics.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Support/BoundedStream.h"
#include "zkc/Support/Refusal.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/TimeProfiler.h"
#include "llvm/Support/raw_ostream.h"
#include <chrono>

using namespace llvm;
namespace zkc {
int runLanguageCompiler(int argc, char **argv) {
  using namespace language;
  std::vector<SourceBuffer> sources;
  TimeTraceScope timing("zkc.language-command");
  std::vector<AssetBuffer> assets;
  std::optional<CapturedProject> captured;
  ArrayRef<SourceBuffer> diagnosticSources;
  std::string entry, subject, format;
  std::optional<EntryKind> entryKind;
  bool declarations = false;
  bool api = false;
  bool sourceClaims = false;
  bool sourceAst = false;
  bool sourceCorrespondence = false;
  bool notations = false;
  NotationInspectionOptions notationOptions;
  EntryOptions options;
  bool cpuTargetSelected = false;
  std::string observationPath;
  bool collectObservations = false;
  std::vector<std::string> dumps;
  std::unique_ptr<CompilationObservation> observation;
  json::Array structuredDiagnostics;
  json::Object identities;
  auto started = std::chrono::steady_clock::now();
  auto publishObservation = [&](bool completed) {
    if (observationPath.empty())
      return true;
    json::Value record =
        observation ? observation->json() : json::Value(json::Object{});
    auto &object = *record.getAsObject();
    object["format"] = "zkc.compilation-observation/0";
    object["completed"] = completed;
    object["inclusive_microseconds"] =
        std::chrono::duration_cast<std::chrono::microseconds>(
            std::chrono::steady_clock::now() - started)
            .count();
    object["diagnostics"] = std::move(structuredDiagnostics);
    object["identities"] = std::move(identities);
    if (captured) {
      object["capture"] = captured->identity();
      json::Array sources;
      for (const auto &source : diagnosticSources)
        sources.push_back(
            json::Object{{"module", source.module},
                         {"path", source.diagnosticPath},
                         {"origin", source.origin == SourceOrigin::Captured
                                        ? "captured"
                                        : "installation"}});
      object["sources"] = std::move(sources);
    }
    std::error_code ec;
    raw_fd_ostream out(observationPath, ec, sys::fs::CD_CreateNew,
                       sys::fs::FA_Write, sys::fs::OF_Text);
    if (ec) {
      errs() << "source.observation-io: " << ec.message() << '\n';
      return false;
    }
    std::string encoded;
    BoundedStream bounded(encoded, 24 * 1024 * 1024);
    bounded << record;
    if (bounded.overflow()) {
      out << json::Value(
                 json::Object{{"format", "zkc.compilation-observation/0"},
                              {"completed", completed},
                              {"truncated", true}})
          << '\n';
    } else
      out << encoded << '\n';
    out.flush();
    if (out.has_error()) {
      errs() << "source.observation-io: " << out.error().message() << '\n';
      out.clear_error();
      return false;
    }
    return true;
  };
  Limits limits;
  auto diagnosticRecord = [](const Diagnostic &message) {
    json::Object record{{"code", message.code}, {"message", message.message}};
    if (message.primary) {
      record["source"] = message.primary->source.index;
      record["begin"] = message.primary->begin;
      record["end"] = message.primary->end;
    }
    json::Array related;
    for (const auto &span : ArrayRef(message.related).take_front(64))
      related.push_back(json::Object{{"source", span.source.index},
                                     {"begin", span.begin},
                                     {"end", span.end}});
    record["related"] = std::move(related);
    if (message.related.size() > 64)
      record["related_truncated"] = true;
    return json::Value(std::move(record));
  };
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
    for (const auto &message : messages) {
      structuredDiagnostics.push_back(diagnosticRecord(message));
    }
    publishObservation(false);
    errs() << formatDiagnostics(messages, diagnosticSources);
    return 1;
  };
  StringRef command(argv[1]);
  if (command != "language-check" && command != "language-emit" &&
      command != "language-interface" && command != "language-bundle" &&
      command != "language-package")
    return refuse(error("source.command", "unknown language command"));
  if (argc > int(limits.files + 13))
    return refuse(error("source.limit", "too many source command arguments"));
  uint64_t total = 0, assetTotal = 0;
  for (int i = 2; i < argc; ++i) {
    StringRef arg(argv[i]);
    if (arg.starts_with("--observations=") ||
        arg.starts_with("--diagnostics=")) {
      collectObservations = arg.starts_with("--observations=");
      arg = arg.split('=').second;
      if (!observationPath.empty() || arg.empty() || arg == "-")
        return refuse(error("source.options", "expected one observation file"));
      observationPath = arg.str();
    } else if (arg.consume_front("--dump=")) {
      SmallVector<StringRef> names;
      arg.split(names, ',');
      for (auto name : names) {
        if (name != "entry" && name != "protocol" && name != "participant" &&
            name != "exec" && name != "execution" && name != "physical")
          return refuse(error("source.options", "unknown dump phase"));
        dumps.push_back(name.str());
      }
    } else if (arg.consume_front("--cpu-target=")) {
      if (cpuTargetSelected)
        return refuse(error("source.options", "CPU target must be unique"));
      auto target = readCpuTarget(arg);
      if (!target)
        return refuse(target.takeError());
      options.cpuTarget = *target;
      cpuTargetSelected = true;
    } else if (arg.consume_front("--source-format=")) {
      if (arg.empty() || !format.empty())
        return refuse(error("source.options",
                            "source format must be nonempty and unique"));
      format = arg.str();
    } else if (arg.consume_front("--entry=")) {
      if (arg.empty() || !entry.empty())
        return refuse(error("source.options",
                            "Entry selection must be nonempty and unique"));
      entry = arg.str();
    } else if (arg.consume_front("--subject=")) {
      if (arg.empty() || !subject.empty())
        return refuse(error("source.options",
                            "subject selection must be nonempty and unique"));
      subject = arg.str();
    } else if (arg.consume_front("--entry-kind=")) {
      if (entryKind || (arg != "function" && arg != "proof") ||
          command == "language-check")
        return refuse(error(
            "source.options",
            "expected one --entry-kind=function|proof for Entry compilation"));
      entryKind = arg == "function" ? EntryKind::Function : EntryKind::Proof;
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
    } else if (arg == "--source-ast") {
      if (sourceAst || command != "language-check")
        return refuse(
            error("source.options",
                  "--source-ast is a check option and may appear once"));
      sourceAst = true;
    } else if (arg == "--source-correspondence") {
      if (sourceCorrespondence || command != "language-check")
        return refuse(error(
            "source.options",
            "--source-correspondence is a check option and may appear once"));
      sourceCorrespondence = true;
    } else if (arg == "--source-claims") {
      if (sourceClaims || command != "language-check")
        return refuse(
            error("source.options",
                  "--source-claims is a check option and may appear once"));
      sourceClaims = true;
    } else if (arg == "--api") {
      if (api || command != "language-check")
        return refuse(error("source.options",
                            "--api is a check option and may appear once"));
      api = true;
    } else if (arg == "--declarations") {
      if (declarations || command != "language-check")
        return refuse(
            error("source.options",
                  "--declarations is a check option and may appear once"));
      declarations = true;
    } else if (arg == "--notations" || arg == "--notation-private" ||
               arg == "--notation-installation") {
      bool &flag = arg == "--notations" ? notations
                   : arg == "--notation-private"
                       ? notationOptions.includePrivate
                       : notationOptions.includeInstallation;
      if (flag || command != "language-check")
        return refuse(error("source.options",
                            arg + " is a check option and may appear once"));
      flag = true;
    } else if (command == "language-check" &&
               (arg == "--no-simplify" || arg == "--release-storage" ||
                arg == "--fuse-vector-reductions" ||
                arg == "--fuse-collect-fold" || arg == "--no-finite-bulk" ||
                arg == "--no-calculation-batching"))
      return refuse(
          error("source.options",
                "checking accepts no executable optimization options"));
    else if (arg == "--no-simplify")
      options.simplify = false;
    else if (arg == "--release-storage")
      options.releaseStorage = true;
    else if (arg == "--no-finite-bulk")
      options.mathematicalSelection.finiteBulk = false;
    else if (arg == "--no-calculation-batching")
      options.mathematicalSelection.calculationBatching = false;
    else if (arg == "--fuse-vector-reductions")
      options.mathematicalSelection.vectorReductionFusion = true;
    else if (arg == "--fuse-collect-fold")
      options.mathematicalSelection.collectFoldFusion = true;
    else
      return refuse(error("source.options", "unknown language option: " + arg));
  }
  if (!notations &&
      (notationOptions.includePrivate || notationOptions.includeInstallation))
    return refuse(error("source.options",
                        "notation visibility options require --notations"));
  if (format.empty())
    return refuse(error("source.options", "--source-format=zkc is required"));
  if (!dumps.empty() && !collectObservations)
    return refuse(error("source.options", "dumps require --observations"));
  if (collectObservations) {
    observation = std::make_unique<CompilationObservation>(dumps);
    options.observations = observation.get();
  }
  if (!subject.empty() && (!entry.empty() || entryKind))
    return refuse(
        error("source.options",
              "--subject is exclusive with --entry and --entry-kind"));
  if (sourceCorrespondence && entry.empty() && subject.empty())
    return refuse(error(
        "source.options",
        "--source-correspondence requires --subject=NAME or --entry=NAME"));
  if (sourceClaims && entry.empty() && subject.empty())
    return refuse(
        error("source.options",
              "--source-claims requires --subject=NAME or --entry=NAME"));
  auto captureResult = capture(std::move(sources), std::move(assets),
                               CaptureOptions{format, limits});
  if (!captureResult)
    return refuse(captureResult.takeError());
  captured = std::move(*captureResult);
  diagnosticSources = captured->sources();
  auto analysis = analyze(*captured);
  diagnosticSources = analysis.sources();
  if (!analysis.diagnostics().empty()) {
    for (const auto &d : analysis.diagnostics())
      structuredDiagnostics.push_back(diagnosticRecord(d));
    publishObservation(false);
    errs() << formatDiagnostics(analysis.diagnostics(), analysis.sources());
    return 1;
  }
  auto project = analysis.checkedProject();
  if (!project)
    return refuse(project.takeError());
  json::Object checked{{"format", "zkc.source-check/0"},
                       {"status", "checked"},
                       {"phase", "complete"},
                       {"scope", !subject.empty() ? "subject"
                                 : entry.empty()  ? "definitions"
                                                  : "entry"},
                       {"capture", captured->identity()},
                       {"installation", project->installationIdentity()}};
  if (command == "language-check") {
    auto inventory = inspectEntries(*project, limits);
    if (!inventory)
      return refuse(inventory.takeError());
    checked["entries"] = cantFail(json::parse(*inventory));
    auto claims = inspectSourceClaimInventory(*project, limits);
    if (!claims)
      return refuse(claims.takeError());
    checked["source_claim_inventory"] = cantFail(json::parse(*claims));
  }
  if (sourceAst) {
    auto report = inspectWrittenSource(*project, limits);
    if (!report)
      return refuse(report.takeError());
    checked["source_ast"] = cantFail(json::parse(*report));
  }
  if (declarations) {
    auto report = inspectDeclarations(*project, limits);
    if (!report)
      return refuse(report.takeError());
    checked["declarations"] = cantFail(json::parse(*report));
  }
  if (notations) {
    auto report = inspectNotations(*project, notationOptions, limits);
    if (!report)
      return refuse(report.takeError());
    checked["notations"] = cantFail(json::parse(*report));
  }
  if (api) {
    auto report = inspectPublicAPI(*project, limits);
    if (!report)
      return refuse(report.takeError());
    checked["api"] = cantFail(json::parse(*report));
  }
  auto publishCheck = [&]() {
    std::string bytes;
    // All optional views share an aggregate ceiling below the SDK process
    // reader's 64 MiB limit. Refusal never publishes a partial JSON document.
    BoundedStream out(bytes, 32 * 1024 * 1024);
    out << json::Value(std::move(checked)) << '\n';
    if (out.overflow())
      return refuse(
          error("source.limit", "source check report byte limit exceeded"));
    if (!publishObservation(true))
      return 1;
    outs() << bytes;
    return 0;
  };
  if (entry.empty() && subject.empty() && command == "language-check") {
    return publishCheck();
  }
  auto selected = subject.empty()
                      ? closeEntry(*project, entry, limits, entryKind)
                      : closeSubject(*project, subject, limits);
  if (!selected)
    return refuse(selected.takeError());
  auto original = prepareOriginal(*selected);
  if (!original)
    return refuse(original.takeError());
  identities["original"] = original->identity();
  identities["installation"] = project->installationIdentity();
  json::Array locations;
  for (const auto &location : original->locations().take_front(4096))
    locations.push_back(json::Object{{"line", location.line},
                                     {"column", location.column},
                                     {"source", location.source.source.index},
                                     {"begin", location.source.begin},
                                     {"end", location.source.end}});
  identities["source_locations"] = std::move(locations);
  identities["source_locations_truncated"] =
      original->locations().size() > 4096;
  if (command == "language-check") {
    checked["entry"] = selected->name();
    // Requested generic specializations are finite, on-demand candidates.
    if (!selected->entry().parameters.empty()) {
      auto *entries = checked.getArray("entries");
      entries->push_back(
          json::Object{{"name", selected->name()}, {"kind", "function"}});
      llvm::sort(*entries, [](const auto &a, const auto &b) {
        return *a.getAsObject()->getString("name") <
               *b.getAsObject()->getString("name");
      });
    }
    checked["original"] = original->identity();
    if (sourceCorrespondence) {
      auto report = exportSourceCorrespondence(*original, limits);
      if (!report)
        return refuse(report.takeError());
      checked["source_correspondence"] = cantFail(json::parse(*report));
    }
    if (sourceClaims) {
      auto report = exportSourceClaims(*original, limits);
      if (!report)
        return refuse(report.takeError());
      checked["source_claims"] = cantFail(json::parse(*report));
    }
    return publishCheck();
  }
  if (command == "language-emit") {
    if (!publishObservation(true))
      return 1;
    outs() << original->bytes();
    return 0;
  }
  if (command == "language-interface") {
    if (!publishObservation(true))
      return 1;
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
    if (!publishObservation(true))
      return 1;
    outs() << package->bytes();
    return 0;
  }
  if (!publishObservation(true))
    return 1;
  outs() << compiled->bytes() << '\n';
  return 0;
}
} // namespace zkc
