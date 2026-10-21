#include "zkc/Compiler/Observation.h"
#include "mlir/IR/Remarks.h"
#include "mlir/Pass/Pass.h"
#include "mlir/Pass/PassInstrumentation.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Support/BoundedStream.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <chrono>
#include <map>
#include <mutex>
#include <set>
using namespace llvm;
using namespace mlir;
namespace zkc {
namespace {
using Clock = std::chrono::steady_clock;
std::string digest(StringRef text) {
  return toHex(SHA256::hash(arrayRefFromStringRef(text)), true);
}
json::Value subject(const mathematical::RealizationSubject &s) {
  json::Array position, occurrences;
  for (auto n : s.position)
    position.push_back(n);
  for (const auto &p : s.occurrence)
    occurrences.push_back(json::Array{p.first, p.second});
  return json::Object{{"declaration", s.declaration},
                      {"site", s.site},
                      {"operation", s.operation},
                      {"position", std::move(position)},
                      {"definition", s.definition},
                      {"original_site", s.originalSite},
                      {"occurrences", std::move(occurrences)}};
}
json::Value capacity(const std::optional<CapacityCause> &c) {
  if (!c)
    return nullptr;
  json::Object result{{"owner", mathematical::decisionName(c->owner)}};
  if (c->requested)
    result["requested"] = *c->requested;
  if (c->available)
    result["available"] = *c->available;
  return result;
}
json::Value policy(const MathematicalSelectionPolicy &p) {
  return json::Object{
      {"finite_bulk", p.finiteBulk},
      {"fuse_vector_reductions", p.vectorReductionFusion},
      {"fuse_collect_fold", p.collectFoldFusion},
      {"calculation_batching", p.calculationBatching},
      {"numerical_expressions",
       p.numericalExpressions == NumericalExpressionMode::PreferNative
           ? "prefer-native"
           : "vector-only"}};
}
json::Value cause(const mathematical::DecisionCause &cause) {
  using namespace mathematical;
  return std::visit(
      [](const auto &c) -> json::Value {
        using T = std::decay_t<decltype(c)>;
        json::Object result;
        if constexpr (std::is_same_v<T, OptimizationOutcome>) {
          result["status"] = decisionName(c.status);
          result["reason"] = decisionName(c.reason);
          if (c.input)
            result["input"] = *c.input;
          if (c.otherInput)
            result["other_input"] = *c.otherInput;
          if (c.axis)
            result["axis"] = *c.axis;
          if (c.otherAxis)
            result["other_axis"] = *c.otherAxis;
        } else if constexpr (std::is_same_v<T, VerificationDecision>) {
          const char *name = "unclassified";
          switch (c.outcome) {
          case VerificationObservation::Verified:
            name = "verified";
            break;
          case VerificationObservation::Mismatch:
            name = "mismatch";
            break;
          case VerificationObservation::OptionalCapacity:
            name = "optional-capacity";
            break;
          case VerificationObservation::RequiredCapacity:
            name = "required-capacity";
            break;
          case VerificationObservation::Unclassified:
            break;
          }
          result["verification"] = name;
          result["detail"] = c.detail;
          result["subject"] = subject(c.subject);
          if (c.invocation)
            result["invocation"] = *c.invocation;
        } else
          result["required_failure"] = c.detail;
        result["capacity"] = capacity(c.capacity);
        return result;
      },
      cause);
}
class RemarkStream : public remark::detail::MLIRRemarkStreamerBase {
  json::Array &records;
  uint64_t &dropped;

public:
  RemarkStream(json::Array &records, uint64_t &dropped)
      : records(records), dropped(dropped) {}
  void streamOptimizationRemark(const remark::detail::Remark &r) override {
    if (records.size() == 4096) {
      ++dropped;
      return;
    }
    json::Array args;
    for (const auto &arg : r.getArgs())
      args.push_back(json::Object{{"key", arg.key}, {"value", arg.val}});
    records.push_back(json::Object{{"name", r.getRemarkName()},
                                   {"kind", r.getRemarkTypeString()},
                                   {"arguments", std::move(args)}});
  }
};
class Instrumentation : public PassInstrumentation {
  CompilationObservation &owner;
  std::mutex mutex;
  std::map<std::pair<Pass *, Operation *>, Clock::time_point> starts;
  json::Array &passes;
  uint64_t &dropped;
  void finish(Pass *pass, Operation *op, bool completed) {
    std::lock_guard<std::mutex> lock(mutex);
    auto key = std::make_pair(pass, op);
    auto found = starts.find(key);
    if (found == starts.end())
      return;
    auto elapsed = std::chrono::duration_cast<std::chrono::microseconds>(
                       Clock::now() - found->second)
                       .count();
    starts.erase(found);
    if (passes.size() == 4096) {
      ++dropped;
      return;
    }
    json::Array statistics;
#if LLVM_ENABLE_STATS
    for (auto *stat : pass->getStatistics().take_front(128))
      statistics.push_back(
          json::Object{{"name", stat->getName()}, {"value", stat->getValue()}});
#endif
    passes.push_back(json::Object{
        {"pass", pass->getArgument()},
        {"operation", op->getName().getStringRef()},
        {"completed", completed},
        {"inclusive_microseconds", elapsed},
        {"statistics", std::move(statistics)},
        {"statistics_enabled", static_cast<bool>(LLVM_ENABLE_STATS)}});
    // These are module passes, so no parallel child mutation can race a dump.
    if (completed && pass->getArgument() == "zkc-lower-math")
      if (auto module = dyn_cast<ModuleOp>(op))
        owner.phase("exec", module);
  }

public:
  Instrumentation(CompilationObservation &owner, json::Array &passes,
                  uint64_t &dropped)
      : owner(owner), passes(passes), dropped(dropped) {}
  void runBeforePass(Pass *p, Operation *op) override {
    std::lock_guard<std::mutex> lock(mutex);
    starts[{p, op}] = Clock::now();
  }
  void runAfterPass(Pass *p, Operation *op) override { finish(p, op, true); }
  void runAfterPassFailed(Pass *p, Operation *op) override {
    finish(p, op, false);
  }
};
} // namespace
struct CompilationObservation::Storage {
  std::set<std::string> dumps;
  json::Array phases, passes, events, remarks;
  uint64_t droppedPasses = 0, droppedEvents = 0, droppedRemarks = 0,
           journals = 0;
};
CompilationObservation::CompilationObservation(std::vector<std::string> dumps)
    : storage(std::make_unique<Storage>()) {
  storage->dumps.insert(dumps.begin(), dumps.end());
}
CompilationObservation::~CompilationObservation() = default;
void CompilationObservation::instrument(PassManager &pm) {
  pm.addInstrumentation(std::make_unique<Instrumentation>(
      *this, storage->passes, storage->droppedPasses));
}
void CompilationObservation::phase(StringRef name, ModuleOp module) {
  if (storage->phases.size() == 32)
    return;
  json::Object record{{"phase", name}};
  uint64_t operations = 0, mappingBytes = 0, omittedLocations = 0;
  json::Object histogram;
  json::Array mapping;
  module.walk([&](Operation *op) {
    ++operations;
    auto key = op->getName().getStringRef();
    auto count = histogram.getInteger(key).value_or(0);
    histogram[key] = count + 1;
    if (mapping.size() == 4096 || mappingBytes >= 1024 * 1024) {
      ++omittedLocations;
      return;
    }
    std::string location;
    BoundedStream out(location, 512);
    op->getLoc().print(out);
    json::Object mapped{{"ordinal", operations - 1},
                        {"operation", key},
                        {"location", location},
                        {"mapping", isa<UnknownLoc>(op->getLoc())
                                        ? "unknown"
                                        : "containing-location"}};
    if (out.overflow())
      mapped["location_truncated"] = true;
    for (StringRef name : {"sym_name", "site", "binding", "implementation",
                           "contract", "arguments", "logical_origin"}) {
      if (auto attr = op->getAttr(name)) {
        std::string text;
        BoundedStream stream(text, 512);
        attr.print(stream);
        mapped[name] = text;
        if (stream.overflow())
          mapped["attributes_truncated"] = true;
      }
    }
    json::Array types;
    for (auto type : op->getResultTypes()) {
      if (types.size() == 8)
        break;
      std::string text;
      BoundedStream stream(text, 512);
      type.print(stream);
      types.push_back(text);
      if (stream.overflow())
        mapped["types_truncated"] = true;
    }
    mapped["result_types"] = std::move(types);
    if (op->getNumResults() > 8)
      mapped["types_truncated"] = true;
    std::string encoded;
    BoundedStream stream(encoded, 16 * 1024);
    json::Value value(std::move(mapped));
    stream << value;
    if (stream.overflow()) {
      ++omittedLocations;
      return;
    }
    mappingBytes += encoded.size();
    mapping.push_back(std::move(value));
  });
  record["operations"] = operations;
  record["histogram"] = std::move(histogram);
  record["locations"] = std::move(mapping);
  record["locations_truncated"] = omittedLocations != 0;
  record["omitted_locations"] = omittedLocations;
  if (storage->dumps.count(name.str())) {
    std::string text;
    BoundedStream out(text, 4 * 1024 * 1024);
    module.print(out, OpPrintingFlags().enableDebugInfo());
    record["ir_truncated"] = out.overflow();
    record["ir"] = text;
    if (!out.overflow())
      record["ir_sha256"] = digest(text);
  }
  storage->phases.push_back(std::move(record));
}
void CompilationObservation::decisions(
    ModuleOp module, const mathematical::RealizationTrace &trace) {
  // Do not replace an embedding application's remark engine. Our temporary
  // engine streams analysis only: a proposal's success is not publication.
  auto &context = *module.getContext();
  bool ownEngine = context.getRemarkEngine() == nullptr;
  if (ownEngine) {
    remark::RemarkCategories categories;
    categories.all = "zkc-mathematics";
    if (failed(remark::enableOptimizationRemarks(
            context,
            std::make_unique<RemarkStream>(storage->remarks,
                                           storage->droppedRemarks),
            std::make_unique<remark::RemarkEmittingPolicyAll>(), categories)))
      ownEngine = false;
  }
  auto cleanup = scope_exit([&] {
    if (ownEngine)
      context.setRemarkEngine(nullptr);
  });
  using namespace mathematical;
  const uint64_t journal = ++storage->journals;
  storage->droppedEvents += trace.droppedEvents;
  for (const auto &event : trace.events) {
    if (storage->events.size() == 4096) {
      ++storage->droppedEvents;
      continue;
    }
    json::Object record{
        {"journal", journal},       {"sequence", event.sequence},
        {"scope", event.scope},     {"parent", event.parent},
        {"service", event.service}, {"subject", subject(event.subject)}};
    std::visit(
        [&](const auto &p) {
          using T = std::decay_t<decltype(p)>;
          if constexpr (std::is_same_v<T, SelectionDecision>) {
            record["kind"] = "selection";
            record["family"] = decisionName(p.family);
            record["choice"] = decisionName(p.choice);
            record["cause"] = cause(p.outcome);
            record["query_subject"] = subject(p.querySubject);
            remark::analysis(module.getLoc(),
                             remark::RemarkOpts::name("MathematicalSelection")
                                 .category("zkc-mathematics"))
                << remark::add("scope {0}: {1} selects {2} ({3}/{4}); "
                               "publication is recorded separately",
                               event.scope, decisionName(p.family),
                               decisionName(p.choice),
                               decisionName(p.outcome.status),
                               decisionName(p.outcome.reason));
          } else if constexpr (std::is_same_v<T, ProposalDecision>) {
            record["kind"] = "proposal";
            record["effective_policy"] = policy(p.effectivePolicy);
          } else if constexpr (std::is_same_v<T, DiscardDecision>) {
            record["kind"] = "discard";
            record["cause"] = cause(p.cause);
          } else if constexpr (std::is_same_v<T, RetryDecision>) {
            record["kind"] = "retry";
            record["discarded_scope"] = p.discardedScope;
            record["effective_policy"] = policy(p.effectivePolicy);
            if (p.occurrence)
              record["occurrence"] = subject(*p.occurrence);
          } else if constexpr (std::is_same_v<T, PublicationDecision>) {
            record["kind"] = "publication";
            record["boundary"] = decisionName(p.boundary);
          } else {
            record["kind"] = "completion";
            record["outcome"] = decisionName(p.outcome);
            if (p.cause)
              record["cause"] = cause(*p.cause);
          }
        },
        event.payload);
    storage->events.push_back(std::move(record));
  }
}
json::Value CompilationObservation::json() const {
  json::Value result(json::Object{{"format", "zkc.compilation-observation/0"}});
  auto &object = *result.getAsObject();
  auto copy = [](const json::Array &value) {
    json::Array result;
    for (const auto &item : value)
      result.push_back(item);
    return json::Value(std::move(result));
  };
  object["phases"] = copy(storage->phases);
  object["passes"] = copy(storage->passes);
  object["decisions"] = copy(storage->events);
  object["remarks"] = copy(storage->remarks);
  object["dropped_passes"] = storage->droppedPasses;
  object["dropped_events"] = storage->droppedEvents;
  object["dropped_remarks"] = storage->droppedRemarks;
  return result;
}
} // namespace zkc
