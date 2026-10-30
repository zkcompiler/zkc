#include "../lib/Transforms/CheckedCandidate.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ScopedFinite.h"
#include "support/ScopedFixture.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Mathematical.h"
#include <fstream>
#include <sstream>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace sf = zkc::test::scopedFinite;

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
      mathematical::CheckedCandidate rejected(*source, sf::prepare(*source));
      bool readActualCandidate = false;
      require(failed(rejected.publish([&](ModuleOp before, ModuleOp after) {
                readActualCandidate =
                    same(before, *original) && !same(after, before);
                return failure();
              })) &&
                  readActualCandidate && same(*source, *original),
              "rejected candidate changed original or bypassed actual reader");
    }
    auto prepared = sf::prepare(*source);
    mathematical::CheckedCandidate accepted(*source, std::move(prepared));
    require(same(*source, *original) &&
                succeeded(accepted.publish(sf::compare)) &&
                !same(*source, *original) &&
                succeeded(sf::compare(*original, *source)),
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
                        "/../structured-source/map-declarations.mlir");
    require(bool(input), "missing map fixture");
    std::ostringstream text;
    text << input.rdbuf();
    auto source = parseSourceString<ModuleOp>(
        replaceText(replaceText(text.str(), "bls12-381.fr", "koala-bear"),
                    "ui255", "ui31"),
        &context);
    require(bool(source), "map fixture refused");
    mathematical::RealizationWork work;
    auto initial = work.requiredFiniteChecking;
    uint64_t copy = 1000000, bytes = 16 * 1024 * 1024;
    std::optional<CapacityCause> capacity;
    auto unchanged = sf::clone(*source);
    auto first =
        protocol::prepareScopedFinite(*source, work, copy, bytes, capacity);
    require(bool(first) && same(*source, *unchanged),
            "first map realization failed");
    auto cost = initial - work.requiredFiniteChecking;
    require(cost > 0, "required collection checking was not charged");
    work.requiredFiniteChecking = cost - 1;
    auto remaining = work.requiredFiniteChecking;
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    mathematical::VerificationDecision outcome;
    auto second = protocol::prepareScopedFinite(
        *source, work, copy, bytes, capacity, {}, nullptr, nullptr, &outcome);
    require(!second && same(*source, *unchanged) &&
                outcome.outcome ==
                    mathematical::VerificationObservation::RequiredCapacity &&
                outcome.capacity && work.requiredFiniteChecking <= remaining,
            "map work reset its allowance or published a refused candidate");
  });
  cases.run("stage observation preserves the checked program", [&] {
    auto source = parseSourceString<ModuleOp>(fixture(), &context);
    require(bool(source), "fixture refused");
    OwningOpRef<ModuleOp> original(cast<ModuleOp>((*source)->clone()));
    auto unobserved = mathematical::prepareProtocol(*source, false);
    require(bool(unobserved), "ordinary preparation failed");
    mathematical::RealizationTrace trace;
    std::string dumps;
    llvm::raw_string_ostream stream(dumps);
    trace.ir = &stream;
    auto observed =
        mathematical::prepareProtocol(*source, false, {}, {}, &trace);
    require(bool(observed) && same(*unobserved, *observed) &&
                same(*source, *original),
            "observation changed the candidate or original");
    const std::vector<std::string> expected{"polynomial-recipes",
                                            "protocol-applications",
                                            "participant-mathematics"};
    bool finiteRequest = false;
    observed->walk([&](exec::FoldOp) { finiteRequest = true; });
    require(finiteRequest && !sf::hasLoop(*observed) &&
                sf::applications(*observed, "vector.dot").empty(),
            "source observation moved numerical selection before execution");
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
    require(dumps.find("Before mathematical stage: protocol-applications") !=
                    std::string::npos &&
                dumps.find("After mathematical stage: participant-mathematics "
                           "(completed)") != std::string::npos,
            "missing labeled IR snapshots");
    // A second invocation starts a fresh trace and records its own policy.
    trace.ir = nullptr;
    auto ordered = mathematical::prepareProtocol(*source, false, {false, true},
                                                 {}, &trace);
    require(bool(ordered) && !trace.policy.finiteBulk &&
                trace.policy.vectorReductionFusion &&
                trace.stages.size() == expected.size(),
            "trace retained old state or reported the wrong effective policy");
  });
  return cases.result();
}
