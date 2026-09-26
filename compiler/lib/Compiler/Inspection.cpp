#include "zkc/Compiler/Inspection.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Protocol/Instantiation.h"
#include "zkc/Source/Codec.h"
#include "zkc/Source/Snapshot.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"

using namespace llvm;
namespace zkc {
Error sourceDiagnostic(const source::Document &document, Error error,
                       const source::Node *record) {
  auto span = record ? document.diagnosticSpan(*record) : std::nullopt;
  const auto file = span ? span->file : 0;
  auto [line, column] = document.lineColumn(span ? span->offset : 0, file);
  std::vector<diagnostics::RefusalInfo> refusals;
  std::vector<InvocationPrecondition> preconditions;
  bool hasSourceError = false;
  visitErrors(error, [&](const ErrorInfoBase &info) {
    if (info.isA<DialectRegistrationError>()) {
      preconditions.push_back(
          static_cast<const DialectRegistrationError &>(info).precondition);
      return;
    }
    hasSourceError = true;
    if (info.isA<Refusal>()) {
      const auto &refusal = static_cast<const Refusal &>(info);
      refusals.push_back({refusal.code, refusal.detail});
    }
  });
  if (!hasSourceError)
    return make_error<CompilationError>(
        toString(std::move(error)), std::move(refusals),
        std::vector<DiagnosticLocation>{}, std::move(preconditions));
  return make_error<CompilationError>(
      (document.filename(file) + ":" + Twine(line) + ":" + Twine(column) +
       ": " + toString(std::move(error)))
          .str(),
      std::move(refusals),
      std::vector<DiagnosticLocation>{
          {document.filename(file).str(), line, column}},
      std::move(preconditions));
}
Expected<json::Value> inspectSource(const source::Document &document,
                                    const frontend::Analysis *analysis) {
  auto *module = document.module();
  if (!module)
    return sourceDiagnostic(document, error("source-format"));
  Expected<json::Value> report = json::Value(nullptr);
  if (module->isLibrary()) {
    const source::Node *failure = nullptr;
    report = generic::inspectLibrary(*module, &failure);
    if (!report)
      return sourceDiagnostic(document, report.takeError(), failure);
  } else {
    if (auto e = frontend::checkProtocolDocument(document))
      return e;
    report = json::Object{{"format", "zkc.source-inspection/1"},
                          {"definitions", json::Array{}},
                          {"configurations", json::Array{}},
                          {"specializations", json::Array{}},
                          {"source", source::encode(*module)}};
  }
  // Paths are coordinates in the portable codec, not semantic traversal.
  source::RecordMap records;
  auto snapshot = source::snapshot(*module, &records);
  if (!snapshot)
    return snapshot.takeError();
  (*report->getAsObject())["selection_template"] =
      json::Array{"zkc.implementation-selection/1", *snapshot, json::Array{}};
  (*report->getAsObject())["snapshot"] = std::move(*snapshot);
  std::map<const source::Node *, source::Path> paths;
  for (const auto &[path, node] : records)
    paths.emplace(node, path);
  json::Array occurrences;
  auto body = [&](const source::Body &instructions, StringRef owner) {
    source::walk(instructions, [&](const source::Instruction &instruction) {
      if (instruction.get<source::Return>() || instruction.get<source::Yield>())
        return;
      json::Array coordinate;
      for (size_t step : paths.at(&instruction))
        coordinate.push_back(int64_t(step));
      json::Value location = nullptr;
      if (auto span = document.span(&instruction)) {
        auto [line, column] = document.lineColumn(span->offset, span->file);
        location = json::Object{{"file", document.filename(span->file).str()},
                                {"line", int64_t(line)},
                                {"column", int64_t(column)},
                                {"length", int64_t(span->length)}};
      }
      occurrences.push_back(json::Object{{"owner", owner.str()},
                                         {"kind", instruction.kind().str()},
                                         {"site", instruction.site},
                                         {"path", std::move(coordinate)},
                                         {"location", std::move(location)}});
    });
  };
  for (const auto &definition : module->definitions)
    body(definition.body, definition.name);
  for (const auto &function : module->functions)
    if (function.body)
      body(*function.body, function.name);
  for (const auto &protocol : module->protocols)
    if (protocol.body)
      body(*protocol.body, protocol.name);
  (*report->getAsObject())["occurrences"] = std::move(occurrences);
  auto calls = analysis ? frontend::inspectProtocolElaboration(*analysis)
                        : frontend::inspectProtocolElaboration(
                              document.text(), document.filename());
  if (!calls)
    return calls.takeError();
  (*report->getAsObject())["elaborated_calls"] = std::move(*calls);
  json::Array requirementOrigins;
  for (const auto &definition : module->definitions)
    for (const auto &requirement : definition.requirements) {
      json::Array arguments;
      for (const auto &argument : requirement.arguments)
        arguments.push_back(argument);
      json::Value location = nullptr;
      if (auto span = document.span(&requirement)) {
        auto [line, column] = document.lineColumn(span->offset, span->file);
        location = json::Object{{"file", document.filename(span->file).str()},
                                {"line", int64_t(line)},
                                {"column", int64_t(column)},
                                {"length", int64_t(span->length)}};
      }
      requirementOrigins.push_back(
          json::Object{{"owner", definition.name},
                       {"predicate", requirement.predicate},
                       {"arguments", std::move(arguments)},
                       {"location", std::move(location)}});
    }
  (*report->getAsObject())["requirement_origins"] =
      std::move(requirementOrigins);
  return report;
}

} // namespace zkc
