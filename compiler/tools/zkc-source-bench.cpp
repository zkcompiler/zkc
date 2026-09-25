#include "../lib/Support/Input.h"
#include "zkc/Source/Codec.h"
#include "zkc/Target/Json.h"
// Bounded API measurements, not a second admission or elaboration path.
#include "zkc/Compiler/Inspection.h"
#include "zkc/Compiler/Instantiation.h"
#include "zkc/Compiler/SourceLocations.h"
#include "zkc/Compiler/TableLibrary.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Protocol/Module.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <chrono>
#include <set>

using namespace llvm;
using Clock = std::chrono::steady_clock;

static json::Object version() {
  return json::Object{{"tool", "zkc-source-bench/1"},
                      {"zkc", ZKC_BENCH_VERSION},
                      {"llvm_mlir", LLVM_VERSION_STRING},
                      {"cxx", __VERSION__},
                      {"build_type", ZKC_BENCH_BUILD_TYPE}};
}

struct Stage {
  std::string name, status = "skipped", diagnostic;
  std::vector<double> samples;
  explicit Stage(std::string name) : name(std::move(name)) {}
  template <typename F> auto run(bool record, F &&action) {
    const auto start = Clock::now();
    auto result = action();
    if (record)
      samples.push_back(
          std::chrono::duration<double, std::micro>(Clock::now() - start)
              .count());
    status = "success";
    return result;
  }
  void refuse(Error error) {
    status = "refused";
    diagnostic = toString(std::move(error));
  }
  json::Object report() const {
    json::Array raw;
    for (double sample : samples)
      raw.push_back(sample);
    json::Object out{{"name", name},
                     {"status", status},
                     {"samples_us", std::move(raw)},
                     {"measured_calls", int64_t(samples.size())}};
    if (!samples.empty()) {
      auto sorted = samples;
      std::sort(sorted.begin(), sorted.end());
      size_t n = sorted.size();
      out["min_us"] = sorted.front();
      out["median_us"] = (sorted[(n - 1) / 2] + sorted[n / 2]) / 2;
    }
    if (!diagnostic.empty())
      out["diagnostic"] = diagnostic;
    return out;
  }
};

int main(int argc, char **argv) {
  if (argc == 2 && StringRef(argv[1]) == "--version") {
    outs() << json::Value(version()) << '\n';
    return 0;
  }
  if (argc == 2 && StringRef(argv[1]) == "--help") {
    outs() << "usage: zkc-source-bench FILE|- [--iterations N] [--warmup N]\n"
              "Measure syntax, source, check, inspect, elaborate, locations "
              "and import "
              "APIs.\n"
              "Accepts .pir or portable JSON; reads at most 1 MiB once.\n"
              "Defaults: 7 iterations, 1 warmup; bounds: 1..1000, 0..100.\n"
              "JSON output retains partial timings on refusal (exit 1).\n"
              "Generic check/inspection repeat elaboration; import repeats "
              "admission.\n"
              "Context setup, reading, serialization and destruction are "
              "outside API timers.\n"
              "Use protocol_experiment.py for durable reproducers and "
              "whole-command time.\n";
    return 0;
  }
  unsigned iterations = 7, warmup = 1;
  if (argc < 2) {
    errs() << "Run zkc-source-bench --help\n";
    return 2;
  }
  for (int i = 2; i < argc; i += 2) {
    unsigned value;
    StringRef option(argv[i]);
    if (i + 1 == argc || StringRef(argv[i + 1]).getAsInteger(10, value) ||
        (option != "--iterations" && option != "--warmup") ||
        (option == "--iterations" && (value == 0 || value > 1000)) ||
        (option == "--warmup" && value > 100)) {
      errs() << "invalid benchmark option; run --help\n";
      return 2;
    }
    (option == "--iterations" ? iterations : warmup) = value;
  }
  Stage syntax{"syntax"}, source{"source"}, check{"check"}, inspect{"inspect"},
      elaborate{"elaborate"}, locations{"locations"}, import{"import"};
  Stage *stages[] = {&syntax,    &source,    &check, &inspect,
                     &elaborate, &locations, &import};
  json::Object result{{"format", "zkc.source-bench/1"},
                      {"versions", version()},
                      {"iterations", iterations},
                      {"warmup", warmup}};
  auto finish = [&](int code) {
    json::Array reports;
    for (const auto *stage : stages)
      reports.push_back(stage->report());
    result["stages"] = std::move(reports);
    result["status"] = code ? "refused" : "success";
    outs() << json::Value(std::move(result)) << '\n';
    return code;
  };
  auto input = zkc::readInput(argv[1], zkc::sourceByteLimit);
  if (!input) {
    result["diagnostic"] = toString(input.takeError());
    return finish(1);
  }
  const auto &text = *input;
  const auto setup = Clock::now();
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  zkc::registerTableLibrary(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  result["context_setup_us"] =
      std::chrono::duration<double, std::micro>(Clock::now() - setup).count();
  for (unsigned i = 0; i < warmup + iterations; ++i) {
    bool measured = i >= warmup;
    auto parsed = syntax.run(measured, [&] {
      return zkc::frontend::checkProtocolSyntax(text, argv[1]);
    });
    if (parsed) {
      syntax.refuse(std::move(parsed));
      return finish(1);
    }
    // This public source-boundary measurement includes parsing and nominal
    // reconstruction. It is not an exclusive sum with the syntax timing.
    auto document = source.run(measured, [&] {
      return zkc::frontend::parseProtocolDocument(text, argv[1]);
    });
    if (!document) {
      source.refuse(document.takeError());
      return finish(1);
    }
    auto checked = check.run(measured, [&] {
      return zkc::frontend::checkProtocolDocument(*document);
    });
    if (checked) {
      check.refuse(std::move(checked));
      return finish(1);
    }
    auto inspection =
        inspect.run(measured, [&] { return zkc::inspectSource(*document); });
    if (!inspection) {
      inspect.refuse(inspection.takeError());
      return finish(1);
    }
    const auto *view = document->module();
    if (!view) {
      elaborate.refuse(zkc::error("interactive-format"));
      return finish(1);
    }
    std::optional<zkc::source::Module> specialized;
    const zkc::source::Module *closed = view;
    if (view->isLibrary()) {
      auto result = elaborate.run(
          measured, [&] { return zkc::generic::elaborateLibrary(*view); });
      if (!result) {
        elaborate.refuse(result.takeError());
        return finish(1);
      }
      specialized = std::move(*result);
      closed = &*specialized;
    } else {
      elaborate.status = "not_applicable";
    }
    auto map = locations.run(
        measured, [&] { return zkc::SourceLocations(*document, context); });
    auto module = import.run(measured, [&] {
      return zkc::protocol::importModule(
          *closed, context,
          [&](const zkc::source::Node &record) { return map(record); });
    });
    if (!module) {
      import.refuse(module.takeError());
      return finish(1);
    }
    if (i + 1 != warmup + iterations)
      continue;
    json::Array metadata;
    zkc::source::RecordMap records;
    auto portable = zkc::source::encode(document->root(), &records);
    size_t spanCount = 0;
    for (const auto &[path, node] : records) {
      auto span = document->span(node);
      if (!span)
        continue;
      ++spanCount;
      json::Array coordinate;
      for (auto index : path)
        coordinate.push_back(int64_t(index));
      metadata.push_back(json::Array{
          std::move(coordinate), int64_t(span->offset), int64_t(span->length)});
    }
    const auto &report = *inspection->getAsObject();
    std::set<std::string> symbols;
    for (const auto &pair : *report.getArray("specializations"))
      symbols.insert((*pair.getAsArray())[1].getAsString()->str());
    std::string ir;
    raw_string_ostream out(ir);
    (*module)->print(out);
    result["sizes"] = json::Object{
        {"input_bytes", int64_t(text.size())},
        {"portable_bytes", int64_t(zkc::printJson(portable).size())},
        {"retained_text_bytes", int64_t(document->text().size())},
        {"span_json_bytes",
         int64_t(zkc::printJson(std::move(metadata)).size())},
        {"filename_bytes", int64_t(document->filename().size())},
        {"closed_portable_bytes",
         int64_t(zkc::printJson(zkc::source::encode(*closed)).size())},
        {"common_mlir_bytes", int64_t(ir.size())}};
    result["counts"] =
        json::Object{{"spans", int64_t(spanCount)},
                     {"source_functions", int64_t(view->functions.size())},
                     {"definitions", int64_t(view->definitions.size())},
                     {"configurations", int64_t(view->configurations.size())},
                     {"demanded_configurations",
                      int64_t(report.getArray("specializations")->size())},
                     {"specializations", int64_t(symbols.size())},
                     {"closed_functions", int64_t(closed->functions.size())},
                     {"protocols", int64_t(view->protocols.size())},
                     {"instances", int64_t(view->instances.size())}};
  }
  return finish(0);
}
