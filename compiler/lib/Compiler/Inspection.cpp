#include "zkc/Compiler/Inspection.h"
#include "InspectionPrinter.h"
#include "zkc/Compiler/Instantiation.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Source/Codec.h"
#include "zkc/Target/Json.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"

using namespace llvm;
namespace zkc {
namespace {
std::string hashSnapshot(const json::Value &source) {
  SHA256 hash;
  hash.update("zkc.source-snapshot/1\n");
  hash.update(printJson(source));
  return toHex(hash.final(), true);
}
} // namespace
Error sourceDiagnostic(const source::Document &document, Error error,
                       const source::Node *record) {
  auto span = document.span(record);
  const auto file = span ? span->file : 0;
  auto [line, column] = document.lineColumn(span ? span->offset : 0, file);
  return createStringError(inconvertibleErrorCode(),
                           (document.filename(file) + ":" + Twine(line) + ":" +
                            Twine(column) + ": " + toString(std::move(error)))
                               .str());
}
Expected<std::string> sourceSnapshot(const source::Module &module) {
  if (auto e = source::checkStructure(module))
    return e;
  return hashSnapshot(source::encode(module));
}
Expected<std::string> sourceSnapshot(const source::Content &content) {
  if (auto e = source::checkStructure(content))
    return e;
  return hashSnapshot(source::encode(content));
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
  auto portable = source::encode(*module, &records);
  auto snapshot = hashSnapshot(portable);
  (*report->getAsObject())["selection_template"] =
      json::Array{"zkc.implementation-selection/1", snapshot, json::Array{}};
  (*report->getAsObject())["snapshot"] = std::move(snapshot);
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

void printSourceInspection(const json::Value &report, raw_ostream &out) {
  const auto &r = *report.getAsObject();
  auto name = [](const json::Value &v) { return *v.getAsString(); };
  auto pairs = [&](const json::Array &values) {
    bool first = true;
    for (const auto &value : values) {
      const auto &pair = *value.getAsArray();
      out << (first ? "" : ", ") << name(pair[0]) << " = " << name(pair[1]);
      first = false;
    }
    if (values.empty())
      out << "none";
  };
  auto predicates = [&](const json::Array &values) {
    bool first = true;
    for (const auto &value : values) {
      const auto &p = *value.getAsArray();
      out << (first ? "" : ", ") << name(p[0]) << "(";
      bool firstArg = true;
      for (const auto &argument : *p[1].getAsArray()) {
        out << (firstArg ? "" : ", ") << name(argument);
        firstArg = false;
      }
      out << ")";
      first = false;
    }
    if (values.empty())
      out << "none";
  };
  out << "Source admitted; implementation search is not performed.\n";
  for (const auto &value : *r.getArray("elaborated_calls")) {
    const auto &call = *value.getAsObject();
    out << "\n"
        << *call.getString("owner") << " [" << *call.getString("site") << "] "
        << *call.getString("kind") << " " << *call.getString("callee")
        << "\n  static arguments (" << *call.getString("static_origin")
        << "): ";
    const auto &arguments = *call.getArray("static_arguments");
    llvm::interleaveComma(arguments, out,
                          [&](const auto &arg) { out << *arg.getAsString(); });
    if (arguments.empty())
      out << "none";
    for (const auto &result : *call.getArray("results")) {
      const auto &binding = *result.getAsObject();
      out << "\n  " << *binding.getString("name") << ": "
          << *binding.getString("type");
    }
    out << '\n';
  }
  for (const auto &value : *r.getArray("definitions")) {
    const auto &d = *value.getAsObject();
    out << "\nfn " << *d.getString("name") << " ("
        << *d.getInteger("operations") << " operations)\n  parameters: ";
    pairs(*d.getArray("parameters"));
    out << "\n  declared requirements: ";
    predicates(*d.getArray("declared"));
    out << "\n  inferred requirements: ";
    predicates(*d.getArray("inferred"));
    out << '\n';
  }
  for (const auto &value : *r.getArray("configurations")) {
    const auto &c = *value.getAsObject();
    out << "\nconfigure " << *c.getString("name") << " = "
        << *c.getString("definition") << "\n  resolved arguments: ";
    pairs(*c.getArray("arguments"));
    out << "\n  remaining parameters: ";
    pairs(*c.getArray("remaining"));
    out << "\n  explicit implementations: ";
    pairs(*c.getArray("implementations"));
    out << "\n  executable use: " << (*c.getBoolean("demanded") ? "yes" : "no")
        << '\n';
  }
  out << "\nDemanded configurations and shared symbols:\n";
  for (const auto &value : *r.getArray("specializations")) {
    const auto &p = *value.getAsArray();
    out << "  " << name(p[0]) << " -> " << name(p[1]) << '\n';
  }
  const auto &module = *r.get("source")->getAsArray();
  out << "\nClosed source: " << module[2].getAsArray()->size()
      << " local functions, " << module[3].getAsArray()->size()
      << " protocols, " << module[4].getAsArray()->size() << " instances, "
      << module[5].getAsArray()->size() << " entries.\n";
}
} // namespace zkc
