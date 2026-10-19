#include "../lib/Transforms/CheckedCandidate.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Finite.h"
#include "zkc/Transforms/Mathematical.h"
#include <fstream>
#include <sstream>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;

namespace {
std::string fixture() {
  std::ifstream input(std::string(ZKC_FINITE_FIXTURES) + "/dot.mlir");
  require(bool(input), "missing fixture");
  std::ostringstream text;
  text << input.rdbuf();
  return text.str();
}
bool same(ModuleOp left, ModuleOp right) {
  return OperationEquivalence::isEquivalentTo(
      left, right, OperationEquivalence::IgnoreLocations);
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run("checked publication and rejected proposal isolation", [&] {
    auto source = parseSourceString<ModuleOp>(fixture(), &context);
    require(bool(source), "fixture refused");
    OwningOpRef<ModuleOp> original(cast<ModuleOp>((*source)->clone()));
    {
      mathematical::CheckedCandidate rejected(*source);
      require(succeeded(finite::realizeLocals(*rejected)),
              "realization failed");
      bool readActualCandidate = false;
      require(failed(rejected.publish([&](ModuleOp before, ModuleOp after) {
                readActualCandidate =
                    same(before, *original) && !same(after, before);
                return failure();
              })) &&
                  readActualCandidate && same(*source, *original),
              "rejected candidate changed original or bypassed actual reader");
    }
    OwningOpRef<ModuleOp> prepared(cast<ModuleOp>((*source)->clone()));
    require(succeeded(finite::realizeLocals(*prepared)), "realization failed");
    mathematical::CheckedCandidate accepted(*source, std::move(prepared));
    require(same(*source, *original) &&
                succeeded(accepted.publish(finite::verifyRealizations)) &&
                !same(*source, *original) &&
                succeeded(finite::verifyRealizations(*original, *source)),
            "checked candidate did not publish its actual realized body");
  });
  cases.run("publication cannot consume the same proposal twice", [&] {
    auto source = parseSourceString<ModuleOp>(fixture(), &context);
    require(bool(source), "fixture refused");
    mathematical::CheckedCandidate candidate(*source);
    require(succeeded(candidate.publish(
                [](ModuleOp, ModuleOp) { return success(); })),
            "first publication failed");
    OwningOpRef<ModuleOp> published(cast<ModuleOp>((*source)->clone()));
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    bool reread = false;
    require(failed(candidate.publish([&](ModuleOp, ModuleOp) {
              reread = true;
              return success();
            })) &&
                !reread && same(*source, *published),
            "repeat publication consumed the already-published body");
  });
  cases.run("module contract changes cannot disappear on publication", [&] {
    auto source = parseSourceString<ModuleOp>(fixture(), &context);
    require(bool(source), "fixture refused");
    mathematical::CheckedCandidate candidate(*source);
    (*candidate)->setAttr("test.changed", UnitAttr::get(&context));
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    bool called = false;
    require(failed(candidate.publish([&](ModuleOp, ModuleOp) {
              called = true;
              return success();
            })) &&
                !called && !(*source)->hasAttr("test.changed"),
            "body-only publication ignored a changed module contract");
  });
  cases.run("required map work is cumulative and refusal is atomic", [&] {
    std::ifstream input(std::string(ZKC_MATH_FIXTURES) +
                        "/map-realization.mlir");
    require(bool(input), "missing map fixture");
    std::ostringstream text;
    text << input.rdbuf();
    auto source = parseSourceString<ModuleOp>(text.str(), &context);
    require(bool(source), "map fixture refused");
    mathematical::RealizationWork work;
    unsigned initial = work.helperOperations;
    OwningOpRef<ModuleOp> first(cast<ModuleOp>((*source)->clone()));
    require(succeeded(mathematical::expandMapRealizations(*first, &work)),
            "first map realization failed");
    unsigned cost = initial - work.helperOperations;
    require(cost > 0, "map helper copy was not charged");
    work.helperOperations = cost - 1;
    auto remaining = work.helperOperations;
    OwningOpRef<ModuleOp> second(cast<ModuleOp>((*source)->clone()));
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    require(failed(mathematical::expandMapRealizations(*second, &work)) &&
                same(*source, *second) && work.helperOperations <= remaining,
            "map work reset its allowance or published a refused candidate");
  });
  cases.run("stage observation preserves the checked program", [&] {
    auto source = parseSourceString<ModuleOp>(fixture(), &context);
    require(bool(source), "fixture refused");
    OwningOpRef<ModuleOp> original(cast<ModuleOp>((*source)->clone()));
    auto unobserved = mathematical::rewriteLocalAlgorithms(*source);
    require(bool(unobserved), "ordinary preparation failed");
    mathematical::RealizationTrace trace;
    std::string dumps;
    llvm::raw_string_ostream stream(dumps);
    trace.ir = &stream;
    auto observed = mathematical::rewriteLocalAlgorithms(*source, {}, &trace);
    require(bool(observed) && same(*unobserved, *observed) &&
                same(*source, *original),
            "observation changed the candidate or original");
    const std::vector<std::string> expected{
        "polynomial-recipes",  "math-realizations",   "retain-computations",
        "nested-contractions", "finite-realizations", "finish-expansion"};
    require(trace.stages.size() == expected.size(), "missing stage records");
    for (size_t i = 0; i < expected.size(); ++i) {
      const auto &stage = trace.stages[i];
      require(stage.name == expected[i] && stage.completed &&
                  stage.operationsBefore && stage.operationsAfter,
              "incorrect stage order or measurement");
      if (i)
        require(trace.stages[i - 1].operationsAfter == stage.operationsBefore,
                "stage accounting lost an intermediate subject");
    }
    stream.flush();
    require(dumps.find("Before mathematical stage: finite-realizations") !=
                    std::string::npos &&
                dumps.find(
                    "After mathematical stage: finish-expansion (completed)") !=
                    std::string::npos,
            "missing labeled IR snapshots");
    // A second invocation starts a fresh trace and records its own policy.
    trace.ir = nullptr;
    auto ordered =
        mathematical::rewriteLocalAlgorithms(*source, {false, true}, &trace);
    require(bool(ordered) && !trace.policy.finiteBulk &&
                trace.policy.vectorReductionFusion &&
                trace.stages.size() == expected.size(),
            "trace retained old state or reported the wrong effective policy");
  });
  return cases.result();
}
