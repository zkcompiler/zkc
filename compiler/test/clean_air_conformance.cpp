// Native finite-AIR side of the Clean export comparison. Test transport: reads
// one zkc.clean-air-control/0 document (common/tests/fixtures/clean) and prints one
// report. The Rust driver consumes the report's per-constraint ring views.
#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/RingExpression.h"
#include "zkc/Relation/AIR.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include "llvm/Support/raw_ostream.h"
#include <fstream>
#include <optional>
#include <set>

using namespace llvm;
using namespace zkc;
using namespace zkc::relation;

namespace {
// Tool limits, below the native AIR/ring limits. The report grows linearly in
// the control, so these bound the output as well.
constexpr size_t byteLimit = 1 << 20;
constexpr unsigned depthLimit = 12;
constexpr size_t componentLimit = 8, subjectLimit = 8, rowLimit = 256,
                 columnLimit = 256;

std::string digest(StringRef text) {
  return toHex(SHA256::hash(arrayRefFromStringRef(text)), true);
}
bool exactKeys(const json::Object &object,
               std::initializer_list<StringRef> keys) {
  if (object.size() != keys.size())
    return false;
  for (auto key : keys)
    if (!object.get(key))
      return false;
  return true;
}
Error shape() { return zkc::error("clean-control-shape"); }

struct Report {
  json::Array disagreements;
  void disagree(StringRef code, StringRef component, StringRef subject,
                std::optional<size_t> row = {},
                std::optional<size_t> constraint = {}) {
    // Owned strings: the report outlives the parsed control.
    json::Object entry{{"code", code.str()},
                       {"component", component.str()},
                       {"subject", subject.str()}};
    if (row)
      entry["row"] = int64_t(*row);
    if (constraint)
      entry["constraint"] = int64_t(*constraint);
    disagreements.push_back(std::move(entry));
  }
};

struct Rows {
  json::Array names;
  AIRTrace trace;
};

Expected<Rows> readRows(const json::Array &rows, StringRef field) {
  if (rows.empty() || rows.size() > rowLimit)
    return zkc::error("clean-control-limit");
  Rows result;
  std::set<std::string> names;
  for (const auto &item : rows) {
    auto *row = item.getAsObject();
    if (!row || !exactKeys(*row, {"name", "cells"}))
      return shape();
    auto name = row->getString("name");
    auto *cells = row->getArray("cells");
    if (!name || !cells || !names.insert(name->str()).second)
      return shape();
    if (result.names.empty()) {
      if (cells->empty() || cells->size() > columnLimit)
        return zkc::error("clean-control-limit");
      result.trace.layout = {field.str(), uint32_t(rows.size()),
                             uint32_t(cells->size())};
    } else if (cells->size() != result.trace.layout.columns) {
      return shape();
    }
    for (const auto &cell : *cells) {
      auto text = cell.getAsString();
      if (!text)
        return shape();
      result.trace.cells.push_back(text->str());
    }
    result.names.push_back(name->str());
  }
  return result;
}

struct Subject {
  json::Object report;
  std::string relationIdentity, arenaIdentity;
};

Expected<Subject> checkSubject(const json::Object &subject, size_t position,
                               StringRef component, StringRef field,
                               const Rows &rows, Report &report) {
  if (!exactKeys(subject, {"name", "reference", "relation", "arena", "rows"}))
    return shape();
  auto name = subject.getString("name");
  auto reference = subject.getString("reference");
  auto *expected = subject.getArray("rows");
  if (!name || !reference || !expected ||
      expected->size() != rows.trace.layout.height ||
      (position == 0) != (*name == "export") ||
      *reference != (position == 0 ? "clean" : "model"))
    return shape();

  // Admission through the same bounded text ingress as relation Assets. The
  // control is canonical, so these bytes are the exact emitted encoding.
  auto relationText = printJson(*subject.get("relation"));
  auto air = readAIRText(relationText);
  if (!air)
    return air.takeError();
  if (air->field() != field || air->publicInputs() != 0 ||
      air->columns() != rows.trace.layout.columns)
    return zkc::error("clean-relation-shape");
  for (size_t c = 0; c < air->constraints().size(); ++c)
    if (air->constraints()[c].scope.kind != AIRScopeKind::Every ||
        air->facts()[c].maxOffset != 0)
      return zkc::error("clean-relation-shape");
  Subject result;
  result.relationIdentity = air->identity();
  if (result.relationIdentity != digest(relationText))
    report.disagree("clean-relation-identity", component, *name);

  auto arenaText = printJson(*subject.get("arena"));
  auto arena = ring::readExpressionText(arenaText);
  if (!arena)
    return arena.takeError();
  if (arena->inputs().size() != air->columns() ||
      arena->outputs().size() != air->constraints().size() ||
      any_of(arena->inputs(),
             [&](const ring::Input &input) { return input.field != field; }))
    return zkc::error("clean-arena-shape");
  result.arenaIdentity = arena->identity();
  if (result.arenaIdentity != digest(arenaText))
    report.disagree("clean-arena-identity", component, *name);

  auto evaluation = air->evaluate(rows.trace, {});
  if (!evaluation)
    return evaluation.takeError();
  size_t height = rows.trace.layout.height,
         constraints = air->constraints().size();
  std::vector<std::vector<std::string>> native(
      height, std::vector<std::string>(constraints));
  for (const auto &residual : evaluation->residuals)
    native[residual.row][residual.constraint] = residual.value;
  json::Array residuals, holds;
  for (size_t row = 0; row < height; ++row) {
    auto *entry = (*expected)[row].getAsObject();
    auto *values = entry ? entry->getArray("residuals") : nullptr;
    auto claimed = entry ? entry->getBoolean("holds") : std::nullopt;
    if (!entry || !exactKeys(*entry, {"residuals", "holds"}) || !values ||
        !claimed || values->size() != constraints)
      return shape();
    bool zero = true, nativeZero = true;
    json::Array nativeRow;
    for (size_t c = 0; c < constraints; ++c) {
      auto value = (*values)[c].getAsString();
      if (!value)
        return shape();
      zero &= *value == "0";
      nativeZero &= native[row][c] == "0";
      if (*value != native[row][c])
        report.disagree("clean-residual", component, *name, row, c);
      nativeRow.push_back(native[row][c]);
    }
    // The control's verdict must be its own residuals' verdict.
    if (*claimed != zero)
      return zkc::error("clean-control-holds");
    if (nativeZero != *claimed)
      report.disagree("clean-verdict", component, *name, row);
    residuals.push_back(std::move(nativeRow));
    holds.push_back(nativeZero);
  }

  // The shared ring arena of each constraint, as consumed by ring providers.
  json::Array views;
  for (uint32_t c = 0; c < constraints; ++c) {
    auto view = air->expressionView(c);
    if (!view)
      return view.takeError();
    json::Array reads;
    for (const auto &input : view->inputs) {
      if (input.kind != AIRExpressionInput::Kind::Read || input.cell.row != 0)
        return zkc::error("clean-binding");
      reads.push_back(json::Array{input.cell.row, input.cell.column});
    }
    views.push_back(json::Object{{"arena", view->expression.encode()},
                                 {"identity", view->expression.identity()},
                                 {"reads", std::move(reads)}});
  }
  result.report = json::Object{{"name", name->str()},
                               {"reference", reference->str()},
                               {"relation_identity", result.relationIdentity},
                               {"arena_identity", result.arenaIdentity},
                               {"satisfied", evaluation->satisfied},
                               {"residuals", std::move(residuals)},
                               {"holds", std::move(holds)},
                               {"views", std::move(views)}};
  return result;
}

Expected<json::Value> check(StringRef text) {
  auto parsed = parseNaturalJson(text, byteLimit, depthLimit,
                                 "clean-control-json", "clean-control-limit");
  if (!parsed)
    return parsed.takeError();
  // One canonical line: every embedded relation and arena is then byte-exact.
  if (printJson(*parsed) + "\n" != text)
    return zkc::error("clean-control-canonical");
  auto *root = parsed->getAsObject();
  if (!root ||
      !exactKeys(*root, {"format", "source", "presentation", "components"}) ||
      root->getString("format") != "zkc.clean-air-control/0")
    return shape();
  auto *source = root->getObject("source");
  auto *presentation = root->getObject("presentation");
  if (!source || !exactKeys(*source, {"repository", "revision"}) ||
      !source->getString("repository") || !source->getString("revision") ||
      !presentation || !exactKeys(*presentation, {"field", "modulus"}))
    return shape();
  auto field = presentation->getString("field");
  auto modulus = presentation->getString("modulus");
  if (!field || !modulus)
    return shape();
  // The control's residue presentation must be an installed prime field.
  auto installed = protocol::fieldModulus(*field);
  if (installed.empty() || installed != *modulus)
    return zkc::error("clean-presentation");
  auto *components = root->getArray("components");
  if (!components)
    return shape();
  if (components->empty() || components->size() > componentLimit)
    return zkc::error("clean-control-limit");

  Report report;
  json::Array results;
  std::set<std::string> componentNames;
  for (const auto &item : *components) {
    auto *component = item.getAsObject();
    if (!component ||
        !exactKeys(*component, {"name", "declaration", "rows", "subjects"}))
      return shape();
    auto name = component->getString("name");
    auto declaration = component->getString("declaration");
    auto *rowArray = component->getArray("rows");
    auto *subjects = component->getArray("subjects");
    if (!name || !declaration || !rowArray || !subjects ||
        !componentNames.insert(name->str()).second)
      return shape();
    auto rows = readRows(*rowArray, *field);
    if (!rows)
      return rows.takeError();
    if (subjects->empty() || subjects->size() > subjectLimit)
      return zkc::error("clean-control-limit");
    json::Array subjectReports;
    std::set<std::string> subjectNames;
    std::string exportRelation, exportArena;
    for (size_t position = 0; position < subjects->size(); ++position) {
      auto *subject = (*subjects)[position].getAsObject();
      if (!subject)
        return shape();
      auto subjectName = subject->getString("name");
      if (!subjectName || !subjectNames.insert(subjectName->str()).second)
        return shape();
      auto checked =
          checkSubject(*subject, position, *name, *field, *rows, report);
      if (!checked)
        return checked.takeError();
      if (position == 0) {
        exportRelation = checked->relationIdentity;
        exportArena = checked->arenaIdentity;
      } else if (checked->relationIdentity == exportRelation ||
                 checked->arenaIdentity == exportArena) {
        // A well-formed mutant is a different artifact, never the export.
        report.disagree("clean-mutant-identity", *name, *subjectName);
      }
      subjectReports.push_back(std::move(checked->report));
    }
    results.push_back(
        json::Object{{"name", name->str()},
                     {"declaration", declaration->str()},
                     {"width", int64_t(rows->trace.layout.columns)},
                     {"rows", std::move(rows->names)},
                     {"subjects", std::move(subjectReports)}});
  }
  bool agreed = report.disagreements.empty();
  return json::Object{
      {"format", "zkc.clean-air-native/0"},
      {"status", agreed ? "pass" : "disagree"},
      {"control_sha256", digest(text)},
      {"presentation",
       json::Object{{"field", field->str()}, {"modulus", modulus->str()}}},
      {"components", std::move(results)},
      {"disagreements", std::move(report.disagreements)}};
}

Expected<std::string> readBounded(StringRef path) {
  std::ifstream stream(path.str(), std::ios::binary);
  if (!stream)
    return zkc::error("clean-control-read");
  std::string text(byteLimit + 1, '\0');
  stream.read(text.data(), text.size());
  text.resize(stream.gcount());
  if (text.size() > byteLimit)
    return zkc::error("clean-control-limit");
  return text;
}
} // namespace

int main(int argc, char **argv) {
  if (argc != 2) {
    errs() << "usage: zkc-clean_air_conformance-test CONTROL\n";
    return 2;
  }
  auto text = readBounded(argv[1]);
  auto report = text ? check(*text) : Expected<json::Value>(text.takeError());
  if (!report) {
    std::string code;
    handleAllErrors(
        report.takeError(),
        [&](const zkc::Refusal &refusal) { code = refusal.code; },
        [&](const ErrorInfoBase &other) { code = other.message(); });
    outs() << printJson(json::Object{{"status", "refused"}, {"code", code}})
           << '\n';
    return 1;
  }
  outs() << printJson(*report) << '\n';
  return report->getAsObject()->getString("status") == "pass" ? 0 : 1;
}
