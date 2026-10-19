#include "../lib/Transforms/Kernel/Support.h"
#include "../lib/Transforms/MathematicalSupport.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/KernelRecipes.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/MathematicalTrace.h"
#include <fstream>
#include <sstream>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
std::string fixture(llvm::StringRef name = "realized-total.mlir") {
  std::ifstream input(std::string(ZKC_FINITE_FIXTURES) + "/" + name.str());
  require(bool(input), "missing total fixture");
  std::ostringstream bytes;
  bytes << input.rdbuf();
  return bytes.str();
}
OwningOpRef<ModuleOp> copy(ModuleOp source) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(source->clone()));
}
bool same(ModuleOp a, ModuleOp b) {
  return OperationEquivalence::isEquivalentTo(
      a, b, OperationEquivalence::IgnoreLocations);
}
protocol_ir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}

void checkConstructionReserve(MLIRContext &context, int copySlack,
                              int siteSlack, bool ampleCopy = false,
                              bool shortDiscardCopy = false,
                              bool shortDiscardSites = false) {
  auto source = parseSourceString<ModuleOp>(
      fixture("../structured-source/realization-finite.mlir"), &context);
  require(bool(source) && succeeded(verify(*source)), "sum source refused");
  auto numerical = kernelRecipeSource(unit(*source), "sum", "calculation");
  auto original = copy(*source);
  OwningOpRef<kernel::ModuleOp> before(
      cast<kernel::ModuleOp>(numerical->clone()));
  constexpr uint64_t copyLimit = 1000000;
  // The two top-level operations each have a 19-byte generated site at "x".
  constexpr uint64_t siteCost = 38;
  mathematical::RealizationWork orderedWork;
  uint64_t orderedRemaining = copyLimit, orderedBytes = siteCost;
  auto ordered =
      kernel::realizeEntry(*numerical, "x", {false, false}, orderedWork,
                           orderedRemaining, orderedBytes, {100000, 1});
  require(bool(ordered) && !orderedBytes,
          "ordered sum did not fit exactly two generated sites");
  const uint64_t copyCost = copyLimit - orderedRemaining;
  require(copyCost > 0, "ordered sum did not charge copying");

  uint64_t remaining = ampleCopy ? copyLimit : copyCost + copySlack;
  uint64_t remainingBytes = siteCost + siteSlack;
  const auto initialCopy = remaining, initialBytes = remainingBytes;
  mathematical::RealizationWork work;
  // Exact discard reserves permit speculation. One unit short must select
  // ordered execution before constructing a proposal, preserving its quotas.
  work.discardedRecipeCopy = initialCopy - unsigned(shortDiscardCopy);
  work.discardedRecipeSiteBytes = initialBytes - unsigned(shortDiscardSites);
  const auto initialWork = work;
  std::string diagnostics;
  ScopedDiagnosticHandler record(&context, [&](Diagnostic &diagnostic) {
    diagnostics += diagnostic.str();
    return success();
  });
  mathematical::RealizationTrace trace;
  auto candidate = kernel::realizeEntry(*numerical, "x", {}, work, remaining,
                                        remainingBytes, {100000, 1}, &trace);
  require(trace.policy.finiteBulk && trace.activeScopes.empty() &&
              trace.remainingWork.discardedRecipeCopy ==
                  work.discardedRecipeCopy &&
              trace.remainingWork.discardedRecipeSiteBytes ==
                  work.discardedRecipeSiteBytes,
          "construction trace lost the original request or cumulative work");
  require(same(*source, *original) &&
              OperationEquivalence::isEquivalentTo(
                  *numerical, *before, OperationEquivalence::IgnoreLocations),
          "construction changed the immutable source");
  require(remaining <= initialCopy && remainingBytes <= initialBytes &&
              work.discardedRecipeCopy <= initialWork.discardedRecipeCopy &&
              work.discardedRecipeSiteBytes <=
                  initialWork.discardedRecipeSiteBytes,
          "construction replenished a cumulative quota");
  if (copySlack < 0 || siteSlack < 0) {
    require(!candidate, "insufficient construction reserve published output");
    require(remaining < initialCopy,
            "terminal construction failure refunded its copying debit");
    return;
  }
  require(bool(candidate), "sum fallback exhausted its construction reserve");
  kernelRecipeOutput(*candidate);
  require(
      diagnostics.empty() && same(*candidate, *ordered) &&
          succeeded(kernel::verifyRecipeOutput(*candidate)) &&
          succeeded(kernel::verifyEntryRecipes(*numerical, *candidate, "x")),
      "sum fallback diagnosed a discarded proposal or lost correspondence");
  require(remaining == initialCopy - copyCost &&
              remainingBytes == initialBytes - siteCost &&
              work.helperOperations == orderedWork.helperOperations &&
              work.helperSlots == orderedWork.helperSlots &&
              work.finiteExpressions == orderedWork.finiteExpressions &&
              work.polynomial == orderedWork.polynomial,
          "fallback did not charge exactly the ordered construction");
  if (shortDiscardCopy || shortDiscardSites) {
    bool reportedCapacity = false;
    for (const auto &event : trace.events)
      if (auto *selection =
              std::get_if<mathematical::SelectionDecision>(&event.payload))
        reportedCapacity |=
            selection->choice == mathematical::RealizationChoice::Ordered &&
            selection->outcome.status == OptimizationStatus::Capacity;
    require(reportedCapacity,
            "discard reservation silently changed the requested policy");
    require(work.discardedRecipeCopy == initialWork.discardedRecipeCopy &&
                work.discardedRecipeSiteBytes ==
                    initialWork.discardedRecipeSiteBytes &&
                work.matching.structural == orderedWork.matching.structural,
            "insufficient discard reserve attempted speculation");
  } else {
    require(work.discardedRecipeCopy < initialWork.discardedRecipeCopy &&
                work.discardedRecipeSiteBytes ==
                    initialWork.discardedRecipeSiteBytes - siteCost &&
                work.matching.structural < orderedWork.matching.structural,
            "discarded construction or recognition work was refunded");
  }
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run("sum fallback retains exactly 38 site bytes with ample copying",
            [&] { checkConstructionReserve(context, 0, 0, true); });
  for (int copySlack : {-1, 0, 1})
    for (int siteSlack : {-1, 0, 1})
      cases.run(
          "sum fallback copy slack " + std::to_string(copySlack) +
              ", site slack " + std::to_string(siteSlack),
          [&] { checkConstructionReserve(context, copySlack, siteSlack); });
  cases.run("insufficient discarded-copy reserve retains ordered construction",
            [&] { checkConstructionReserve(context, 0, 0, false, true); });
  cases.run(
      "insufficient discarded-site reserve retains ordered construction",
      [&] { checkConstructionReserve(context, 0, 0, false, false, true); });
  cases.run("discarded construction stays cumulative across calls", [&] {
    auto source = parseSourceString<ModuleOp>(
        fixture("../structured-source/realization-finite.mlir"), &context);
    require(bool(source), "sum source refused");
    auto numerical = kernelRecipeSource(unit(*source), "sum", "calculation");
    auto original = copy(*source);
    OwningOpRef<kernel::ModuleOp> before(
        cast<kernel::ModuleOp>(numerical->clone()));
    mathematical::RealizationWork work;
    uint64_t remaining = 1000000, remainingBytes = 76;
    work.discardedRecipeSiteBytes = remainingBytes;
    unsigned diagnostics = 0;
    ScopedDiagnosticHandler record(&context, [&](Diagnostic &) {
      ++diagnostics;
      return success();
    });
    for (unsigned call = 0; call != 2; ++call) {
      const auto beforeWork = work;
      auto candidate = kernel::realizeEntry(
          *numerical, "x", {}, work, remaining, remainingBytes, {100000, 1});
      require(bool(candidate), "shared construction reserve refused sum");
      require(remainingBytes == 38 * (1 - call) &&
                  work.discardedRecipeSiteBytes == remainingBytes &&
                  work.discardedRecipeCopy < beforeWork.discardedRecipeCopy &&
                  work.matching.structural < beforeWork.matching.structural,
              "a later call reset discarded construction or recognition work");
    }
    require(
        !diagnostics && same(*source, *original) &&
            OperationEquivalence::isEquivalentTo(
                *numerical, *before, OperationEquivalence::IgnoreLocations),
        "repeated fallback diagnosed a discarded proposal or changed source");
  });
  for (bool nested : {false, true}) {
    cases.run(
        nested ? "nested total finite comparison retries ordered"
               : "total finite comparison retries ordered",
        [&] {
          auto text = fixture();
          if (!nested) {
            auto pos = text.find("step=@outside");
            require(pos != std::string::npos, "missing outer step");
            text.replace(pos, std::string("step=@outside").size(),
                         "step=@inside");
          }
          auto source = parseSourceString<ModuleOp>(text, &context);
          require(bool(source) && succeeded(verify(*source)),
                  "total source refused");
          auto numerical =
              kernelRecipeSource(unit(*source), "total", "calculation");
          auto original = copy(*source);
          OwningOpRef<kernel::ModuleOp> before(
              cast<kernel::ModuleOp>(numerical->clone()));
          mathematical::RealizationWork work, orderedWork, bulkWork;
          const auto initialWork = work;
          auto bulk =
              realizeKernelEntry(*numerical, "calculation", {}, bulkWork);
          require(bool(bulk), "ordinary bulk path refused");
          kernelRecipeOutput(*bulk);
          require(bulkWork.discardedRecipeCopy ==
                          initialWork.discardedRecipeCopy &&
                      bulkWork.discardedRecipeSiteBytes ==
                          initialWork.discardedRecipeSiteBytes,
                  "selected bulk construction spent the discard reserve");
          auto ordered = realizeKernelEntry(*numerical, "calculation",
                                            {false, false}, orderedWork);
          require(bool(ordered), "ordered total path refused");
          kernelRecipeOutput(*ordered);
          require(!same(*bulk, *ordered),
                  "fixture did not select optional bulk work");
          unsigned diagnostics = 0;
          ScopedDiagnosticHandler record(&context, [&](Diagnostic &) {
            ++diagnostics;
            return success();
          });
          auto candidate = realizeKernelEntry(*numerical, "calculation", {},
                                              work, {100000, 1});
          require(bool(candidate),
                  "optional total comparison exhaustion refused");
          kernelRecipeOutput(*candidate);
          require(
              !diagnostics && same(*candidate, *ordered) &&
                  succeeded(kernel::verifyRecipeOutput(*candidate)) &&
                  same(*source, *original) &&
                  OperationEquivalence::isEquivalentTo(
                      *numerical, *before,
                      OperationEquivalence::IgnoreLocations),
              "retry diagnosed a discarded proposal or changed source/output");
          require(succeeded(kernel::verifyEntryRecipes(*numerical, *candidate,
                                                       "calculation")),
                  "fallback lost original helper correspondence");
          require(work.helperOperations == orderedWork.helperOperations &&
                      work.helperSlots == orderedWork.helperSlots,
                  "optional attempt consumed required fallback reserve");
          require(work.matching.structural < orderedWork.matching.structural,
                  "discarded optional recognition work was replenished");
        });
  }
  cases.run("required total reader exhaustion refuses atomically", [&] {
    auto source = parseSourceString<ModuleOp>(fixture(), &context);
    require(bool(source), "total source refused");
    auto numerical = kernelRecipeSource(unit(*source), "total", "calculation");
    auto original = copy(*source);
    OwningOpRef<kernel::ModuleOp> before(
        cast<kernel::ModuleOp>(numerical->clone()));
    std::string diagnostics;
    ScopedDiagnosticHandler record(&context, [&](Diagnostic &diagnostic) {
      diagnostics += diagnostic.str();
      return success();
    });
    mathematical::RealizationWork work;
    const auto initialWork = work;
    auto candidate =
        realizeKernelEntry(*numerical, "calculation", {}, work, {0, 100000});
    require(!candidate && same(*source, *original) &&
                OperationEquivalence::isEquivalentTo(
                    *numerical, *before, OperationEquivalence::IgnoreLocations),
            "required capacity published a partial total body");
    require(diagnostics.find("finite-verification-capacity") !=
                std::string::npos,
            "required capacity lost its diagnostic");
    require(work.discardedRecipeCopy == initialWork.discardedRecipeCopy &&
                work.discardedRecipeSiteBytes ==
                    initialWork.discardedRecipeSiteBytes,
            "required capacity incorrectly retried as optional exhaustion");
  });
  return cases.result();
}
