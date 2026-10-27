#include "../lib/Transforms/Kernel/Support.h"
#include "../lib/Transforms/LaneRealization.h"
#include "../lib/Transforms/MathematicalSupport.h"
#include "../lib/Transforms/RealizationTrace.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/KernelRecipes.h"
#include "support/NativeCases.h"
#include "support/ScopedFinite.h"
#include "zkc/Analysis/Computation.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Kernel.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include <fstream>
#include <sstream>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
using namespace zkc::mathematical;
namespace {
protocol_ir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
OwningOpRef<ModuleOp> fixture(MLIRContext &context, StringRef name,
                              bool math = false) {
  std::ifstream input(
      std::string(math ? ZKC_MATH_FIXTURES : ZKC_FINITE_FIXTURES) + "/" +
      name.str() + ".mlir");
  require(bool(input), "missing fixture");
  std::ostringstream bytes;
  bytes << input.rdbuf();
  auto source = parseSourceString<ModuleOp>(bytes.str(), &context);
  require(bool(source) && succeeded(verify(*source)), "fixture refused");
  return source;
}
OwningOpRef<ModuleOp> copy(ModuleOp source) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(source->clone()));
}
bool same(ModuleOp a, ModuleOp b) {
  return OperationEquivalence::isEquivalentTo(
      a, b, OperationEquivalence::IgnoreLocations);
}
bool sameWork(const RealizationWork &a, const RealizationWork &b) {
  return a.matching.structural == b.matching.structural &&
         a.matching.equations == b.matching.equations &&
         a.matching.evidence == b.matching.evidence && a.lanes == b.lanes &&
         a.helperOperations == b.helperOperations &&
         a.helperSlots == b.helperSlots && a.polynomial == b.polynomial &&
         a.finiteExpressions == b.finiteExpressions &&
         a.collectFoldDiscovery == b.collectFoldDiscovery &&
         a.discardedRecipeCopy == b.discardedRecipeCopy &&
         a.discardedRecipeSiteBytes == b.discardedRecipeSiteBytes &&
         a.discardedRecipeExpansion == b.discardedRecipeExpansion &&
         a.requiredMapChecking == b.requiredMapChecking &&
         a.optionalMapChecking == b.optionalMapChecking &&
         a.numericalContextChecking == b.numericalContextChecking &&
         a.numericalCheckCopy == b.numericalCheckCopy &&
         a.numericalCheckSiteBytes == b.numericalCheckSiteBytes &&
         a.requiredMapConstruction == b.requiredMapConstruction &&
         a.optionalMapConstruction == b.optionalMapConstruction &&
         a.requiredFiniteChecking == b.requiredFiniteChecking &&
         a.optionalFiniteChecking == b.optionalFiniteChecking &&
         a.selectionBookkeeping == b.selectionBookkeeping &&
         a.numericalSelection == b.numericalSelection &&
         a.numericalOccurrence == b.numericalOccurrence;
}
template <class T>
std::vector<const RealizationEvent *> events(const RealizationTrace &trace) {
  std::vector<const RealizationEvent *> result;
  for (const auto &event : trace.events)
    if (std::holds_alternative<T>(event.payload))
      result.push_back(&event);
  return result;
}
void checkRetry(const RealizationTrace &trace, StringRef service) {
  auto retries = events<RetryDecision>(trace);
  require(retries.size() == 1 && retries[0]->service == service,
          "missing or duplicated retry");
  const auto &retry = std::get<RetryDecision>(retries[0]->payload);
  require(trace.policy.finiteBulk &&
              (retry.occurrence ? retry.effectivePolicy.finiteBulk
                                : !retry.effectivePolicy.finiteBulk),
          "effective fallback overwrote requested policy");
  const RealizationEvent *discard = nullptr;
  for (auto *event : events<DiscardDecision>(trace))
    if (event->scope == retry.discardedScope)
      discard = event;
  require(discard && discard->sequence < retries[0]->sequence,
          "retry did not follow a discarded attempt");
  auto *verification = std::get_if<VerificationDecision>(
      &std::get<DiscardDecision>(discard->payload).cause);
  require(verification &&
              verification->outcome ==
                  VerificationObservation::OptionalCapacity &&
              verification->capacity &&
              verification->capacity->owner == WorkOwner::OptionalComparison &&
              !verification->subject.operation.empty(),
          "optional reader cause or actual subject was lost");
  require(!retry.occurrence || *retry.occurrence == verification->subject,
          "targeted retry lost the independently reported occurrence");
  const RealizationEvent *later = nullptr;
  for (auto *event : events<ProposalDecision>(trace))
    if (event->service == service && event->sequence > retries[0]->sequence)
      later = event;
  require(later && later->scope != discard->scope &&
              later->parent == discard->parent &&
              later->subject == discard->subject,
          "retry changed immutable source identity or transaction scope");
  for (auto *event : events<PublicationDecision>(trace))
    require(event->scope != discard->scope,
            "discarded attempt claimed publication");
  bool repeatedSubject = false;
  for (auto *first : events<SelectionDecision>(trace)) {
    if (std::get<SelectionDecision>(first->payload).outcome.status !=
        OptimizationStatus::Succeeded)
      continue;
    for (auto *second : events<SelectionDecision>(trace))
      if (std::get<SelectionDecision>(second->payload).outcome.reason ==
              OptimizationReason::OrderedRetry &&
          first->subject == second->subject)
        repeatedSubject = true;
  }
  require(repeatedSubject, "ordered retry lost the selected subject identity");
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  auto prepare = [&](ModuleOp source, RealizationWork &work,
                     MathematicalSelectionPolicy policy = {},
                     RealizationTrace *trace = nullptr) {
    uint64_t copy = 1000000, bytes = 16 * 1024 * 1024;
    std::optional<CapacityCause> capacity;
    return protocol::prepareScopedFinite(source, work, copy, bytes, capacity,
                                         policy, nullptr, nullptr, nullptr,
                                         mathematicalRecipes(), trace);
  };
  for (auto name : {"dot", "collect"})
    cases.run(std::string("finite retry ") + name, [&, name] {
      auto original = fixture(context, name), before = copy(*original);
      RealizationWork work, orderedWork, unobservedWork;
      work.requiredFiniteChecking = unobservedWork.requiredFiniteChecking =
          100000;
      work.optionalFiniteChecking = unobservedWork.optionalFiniteChecking = 1;
      RealizationTrace trace;
      auto ordered = prepare(*original, orderedWork, {false, false});
      auto source = prepare(*original, work, {}, &trace);
      auto unobserved = prepare(*original, unobservedWork);
      require(ordered && source && unobserved && same(*source, *ordered) &&
                  same(*source, *unobserved) &&
                  sameWork(work, unobservedWork) && same(*original, *before),
              "observation changed retry behavior or accounting");
      require(work.matching.equations < orderedWork.matching.equations &&
                  work.helperOperations == orderedWork.helperOperations &&
                  work.helperSlots == orderedWork.helperSlots,
              "retry replenished optional work or consumed required reserve");
      checkRetry(trace, "scoped-finite-attempt");
      auto publications = events<PublicationDecision>(trace);
      require(
          llvm::count_if(
              publications,
              [](const RealizationEvent *event) {
                return event->parent == 0 &&
                       std::get<PublicationDecision>(event->payload).boundary ==
                           PublicationBoundary::ReturnedCandidate;
              }) == 1,
          "standalone finite service lost its returned candidate");
      require(trace.activeScopes.empty() && sameWork(trace.remainingWork, work),
              "trace retained active scope or incorrect final balance");
    });
  cases.run("bounded scoped diagnostics preserve retry and work", [&] {
    auto source = fixture(context, "dot"), before = copy(*source);
    RealizationWork controlWork;
    controlWork.requiredFiniteChecking = 100000;
    controlWork.optionalFiniteChecking = 1;
    auto control = prepare(*source, controlWork);
    require(bool(control), "unobserved retry control refused");
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    for (size_t limit : {size_t(0), size_t(2)})
      for (unsigned mode = 0; mode < 3; ++mode) {
        RealizationWork work;
        work.requiredFiniteChecking = 100000;
        work.optionalFiniteChecking = 1;
        RealizationTrace trace;
        trace.eventLimit = limit;
        trace.remarks = mode == 1;
        std::string text;
        llvm::raw_string_ostream stream(text);
        trace.ir = mode == 2 ? &stream : nullptr;
        auto candidate = prepare(*source, work, {}, &trace);
        require(candidate && same(*candidate, *control) &&
                    same(*source, *before) && sameWork(work, controlWork) &&
                    sameWork(trace.remainingWork, work),
                "bounded diagnostics changed retry output or work");
        require(trace.events.size() == limit && trace.droppedEvents &&
                    trace.activeScopes.empty() &&
                    trace.declarationOrigins.empty(),
                "bounded diagnostics lost truncation or retained scope state");
      }
  });
  cases.run("lane capacity retains ordered realization and typed decline", [&] {
    auto source = fixture(context, "collect");
    RealizationTrace trace;
    RealizationWork work, orderedWork;
    work.lanes = 0;
    MathematicalSelectionPolicy policy;
    policy.numericalExpressions = NumericalExpressionMode::VectorOnly;
    auto candidate = prepare(*source, work, policy, &trace);
    auto ordered = prepare(*source, orderedWork, {false, false});
    require(candidate && ordered && same(*candidate, *ordered),
            "lane decline changed the fallback");
    bool declined = false;
    for (auto *event : events<SelectionDecision>(trace)) {
      const auto &selection = std::get<SelectionDecision>(event->payload);
      if (selection.family == DecisionFamily::Lanes) {
        require(selection.choice == RealizationChoice::Ordered &&
                    selection.outcome.status == OptimizationStatus::Capacity &&
                    selection.outcome.capacity->owner == WorkOwner::Lanes &&
                    selection.outcome.capacity->available == 0 &&
                    selection.outcome.capacity->requested,
                "lane failed debit lost precision");
        declined = true;
      }
    }
    require(declined && events<RetryDecision>(trace).empty(),
            "lane fallback masqueraded as retry");
  });
  cases.run("unsupported lane construction emits no payload", [&] {
    auto source = fixture(context, "collect");
    finite::Computation computation;
    auto declaration = &scopedFinite::function(*source, "work").front().front();
    require(declaration &&
                succeeded(finite::describe(declaration, computation)),
            "missing collect");
    llvm::DenseMap<Value, LaneInput> inputs;
    uint64_t work = 100000;
    unsigned emitted = 0;
    auto result = realizeLanes(
        computation.helper->getRegion(0).front(), inputs,
        computation.signature.getResult(0), {}, &work, mathematicalRecipes(),
        [&](StringRef, ValueRange, Type, ArrayRef<std::string>) {
          ++emitted;
          return Value();
        });
    require(bool(result),
            "unsupported lane formula became a construction error");
    require(result->status == LaneRealizationStatus::Unsupported && !emitted &&
                result->outcome.status == OptimizationStatus::Unsupported &&
                work > 0,
            "unsupported lane formula emitted or became capacity");
  });
  cases.run("required finite failure has no retry or publication", [&] {
    auto source = fixture(context, "dot"), before = copy(*source);
    RealizationTrace trace;
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    RealizationWork work;
    work.requiredFiniteChecking = 0;
    auto candidate = prepare(*source, work, {}, &trace);
    require(!candidate && same(*source, *before),
            "required capacity published a candidate");
    auto discards = events<DiscardDecision>(trace);
    require(discards.size() == 1 && events<RetryDecision>(trace).empty() &&
                events<PublicationDecision>(trace).empty(),
            "required failure retried or published");
    const auto *cause = std::get_if<VerificationDecision>(
        &std::get<DiscardDecision>(discards[0]->payload).cause);
    require(
        cause && cause->outcome == VerificationObservation::RequiredCapacity &&
            cause->capacity->owner == WorkOwner::RequiredFiniteReader &&
            cause->capacity->requested == 1 && cause->capacity->available == 0,
        "required reader capacity became a recognition failure");
  });
  cases.run("scoped helper expansion remains deferred until realization", [&] {
    auto source = fixture(context, "total-collect"), original = copy(*source);
    RealizationTrace trace;
    auto candidate = prepareProtocol(*source, false, {}, {}, &trace);
    unsigned collections = 0;
    if (candidate)
      candidate->walk([&](algebra::FiniteCollectOp) { ++collections; });
    require(candidate && same(*source, *original) && collections == 1 &&
                trace.remainingWork.helperOperations ==
                    trace.initialWork.helperOperations,
            "preparation expanded a retained map or changed its source");
    require(events<DiscardDecision>(trace).empty() &&
                trace.activeScopes.empty(),
            "successful preparation retained a discarded or active scope");
    PassManager demand(&context);
    demand.addPass(protocol::createProjectProtocolPass(false));
    demand.addPass(protocol::createLowerMathPass());
    require(succeeded(demand.run(*candidate)), "map demand formation refused");
    exec::ComputeOp request;
    candidate->walk([&](exec::ComputeOp op) { request = op; });
    require(bool(request), "map demand lost its mathematical request");
    SymbolTableCollection symbols;
    auto entry = request.resolveCallee(symbols);
    auto numerical = cast<ModuleOp>(entry->getParentOp());
    auto prepared = copy(*candidate);
    RealizationWork positiveWork;
    require(bool(realizeKernelEntry(numerical, request.getSite(),
                                    {false, false}, positiveWork)),
            "unbounded map realization control refused");
    RealizationTrace mapTrace;
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    RealizationWork work;
    work.helperOperations = 0;
    auto refused = realizeKernelEntry(numerical, request.getSite(),
                                      {false, false}, work, {}, &mapTrace);
    require(
        !refused && same(*candidate, *prepared) &&
            events<RetryDecision>(mapTrace).empty() &&
            events<PublicationDecision>(mapTrace).empty(),
        "required helper expansion retried, published or changed its source");
    bool failedHelper = false;
    for (auto *event : events<CompletionDecision>(mapTrace)) {
      auto &completion = std::get<CompletionDecision>(event->payload);
      if (!completion.cause)
        continue;
      auto *cause = std::get_if<RequiredFailure>(&*completion.cause);
      failedHelper |= cause && cause->capacity &&
                      cause->capacity->owner == WorkOwner::HelperOperations &&
                      cause->capacity->available == 0;
    }
    require(failedHelper, "late helper failure lost its typed capacity cause");
  });
  for (bool nested : {false, true})
    cases.run(nested ? "nested total retry" : "ordinary total retry", [&,
                                                                       nested] {
      auto source = fixture(context, "realized-total");
      if (!nested) {
        auto unit =
            cast<protocol_ir::ProtocolModuleOp>(source->getBody()->front());
        auto total = SymbolTable(unit).lookup<func::FuncOp>("total");
        total.walk([&](algebra::FiniteFoldOp op) {
          op->setAttr("step", FlatSymbolRefAttr::get(&context, "inside"));
        });
      }
      require(succeeded(verify(*source)), "total control refused");
      auto numerical =
          kernelRecipeSource(unit(*source), "total", "calculation");
      // Force allocation of a different working name in the nested case.
      if (nested) {
        auto reserved = cast<func::FuncOp>(
            mathematical::getComputationEntry(*numerical)->clone());
        reserved.setSymName("_recipe_entry");
        reserved.setPrivate();
        numerical->getBody()->push_back(reserved);
      }
      auto original = copy(*source);
      OwningOpRef<mlir::ModuleOp> before(
          cast<mlir::ModuleOp>(numerical->clone()));
      RealizationTrace trace;
      RealizationWork work, controlWork, orderedWork;
      auto ordered = realizeKernelEntry(*numerical, "calculation",
                                        {false, false}, orderedWork);
      auto observed = realizeKernelEntry(*numerical, "calculation", {}, work,
                                         {100000, 1}, &trace);
      auto unobserved = realizeKernelEntry(*numerical, "calculation", {},
                                           controlWork, {100000, 1});
      require(
          ordered && observed && unobserved && same(*observed, *ordered) &&
              same(*observed, *unobserved) && sameWork(work, controlWork) &&
              same(*source, *original) &&
              OperationEquivalence::isEquivalentTo(
                  *numerical, *before, OperationEquivalence::IgnoreLocations) &&
              succeeded(kernel::verifyEntryRecipes(*numerical, *observed,
                                                   "calculation")),
          "total retry changed IR, checking, or accounting");
      kernelRecipeOutput(*ordered);
      kernelRecipeOutput(*observed);
      kernelRecipeOutput(*unobserved);
      require(work.matching.structural < orderedWork.matching.structural,
              "total retry replenished matching work");
      checkRetry(trace, "kernel-recipe-attempt");
      auto publications = events<PublicationDecision>(trace);
      require(llvm::count_if(publications,
                             [](const RealizationEvent *event) {
                               return event->parent == 0 &&
                                      event->service == "kernel-recipes";
                             }) == 1 &&
                  trace.activeScopes.empty() &&
                  trace.declarationOrigins.empty() &&
                  sameWork(trace.remainingWork, work),
              "Kernel recipe service lost its publication or final balance");
      bool observedEntry = false;
      for (auto *event : events<SelectionDecision>(trace))
        if (event->subject.site == kernelRecipeSite("calculation", 0)) {
          require(event->subject.declaration == "calculation" &&
                      event->subject.position.empty(),
                  "working entry name escaped into the recipe trace");
          observedEntry = true;
        }
      require(observedEntry, "recipe trace lost the original entry occurrence");
    });
  cases.run(
      "declaration origins follow observer scopes and sequential reuse", [&] {
        auto source = fixture(context, "dot"), before = copy(*source);
        auto *op = &scopedFinite::function(*source, "work").front().front();
        auto *fold = scopedFinite::function(*source, "step").getOperation();
        auto original = realizationSubject(op), expected = original;
        expected.declaration = "original";
        RealizationTrace trace;
        RealizationWork work, initial = work;
        std::string text, remarks;
        llvm::raw_string_ostream stream(text);
        trace.ir = &stream;
        trace.remarks = true;
        ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
          llvm::raw_string_ostream out(remarks);
          diagnostic.print(out);
          return success();
        });
        {
          RealizationScope outer(&trace, "origin-parent", op, {}, &work);
          outer.declarationOrigin("work", "original");
          outer.declarationOrigin("step", "original_fold");
          finite::ComputationDiagnostic diagnostic;
          diagnostic.subject = op;
          diagnostic.occurrencePath = {op, fold};
          {
            RealizationScope child(&trace, "origin-child", op);
            child.selectionDiagnostic(op, DecisionFamily::Finite,
                                      RealizationChoice::Ordered, diagnostic);
            const auto &event = trace.events.back();
            auto query = expected;
            query.occurrence = {{original.site, "original"},
                                {"func.func", "original_fold"}};
            require(
                event.subject == expected &&
                    std::get<SelectionDecision>(event.payload).querySubject ==
                        query,
                "inherited origins changed identity fields or occurrence "
                "paths");
            child.declarationOrigin("work", "nested");
            outer.selectionDiagnostic(op, DecisionFamily::Finite,
                                      RealizationChoice::Ordered, diagnostic);
            require(trace.events.back().subject == expected &&
                        std::get<SelectionDecision>(trace.events.back().payload)
                                .querySubject == query,
                    "nested origin changed an enclosing scope's observation");
            child.failure(
                VerificationDecision{VerificationObservation::Mismatch,
                                     "nested refusal",
                                     {},
                                     original});
            child.complete(CompletionKind::Refused);
            const auto &completion = trace.events.back();
            const auto &cause =
                *std::get<CompletionDecision>(completion.payload).cause;
            require(
                completion.subject.declaration == "nested" &&
                    std::get<VerificationDecision>(cause).subject.declaration ==
                        "nested",
                "nested origin did not reach completion and its cause");
          }
          auto refuse = [&] {
            RealizationScope refused(&trace, "origin-refusal", op);
            refused.declarationOrigin("work", "refused");
            refused.propose();
            refused.failure(
                VerificationDecision{VerificationObservation::Mismatch,
                                     "early refusal",
                                     {},
                                     original});
          };
          refuse();
          const auto &discard =
              std::get<DiscardDecision>(trace.events.back().payload);
          require(std::get<VerificationDecision>(discard.cause)
                          .subject.declaration == "refused",
                  "early refusal lost its scoped origin");
          // A source spelling can also name another temporary declaration.
          // Origin resolution is one lookup, not a transitive rename chain.
          outer.declarationOrigin("original", "unrelated");
          auto occurrence = original;
          occurrence.definition = "definition";
          occurrence.originalSite = "authored";
          occurrence.occurrence = {{"call", "work"}};
          outer.selection(occurrence, DecisionFamily::Finite,
                          RealizationChoice::Ordered, {});
          expected.definition = "definition";
          expected.originalSite = "authored";
          expected.occurrence = {{"call", "original"}};
          require(trace.events.back().subject == expected,
                  "origin restoration or source occurrence lookup failed");
          outer.complete();
        }
        require(
            trace.activeScopes.empty() && trace.declarationOrigins.empty() &&
                same(*source, *before) && sameWork(work, initial) &&
                sameWork(trace.remainingWork, work),
            "observer origins escaped their scope or changed IR/accounting");
        for (const auto *rendered : {&text, &remarks})
          require(rendered->find("subject=@original") != std::string::npos &&
                      rendered->find("subject=@nested") != std::string::npos &&
                      rendered->find("subject=@work") == std::string::npos,
                  "rendered decisions disagreed with recorded source identity");
        {
          RealizationScope reused(&trace, "origin-reused", op);
          reused.complete();
        }
        require(trace.events.size() == 1 &&
                    trace.events.front().sequence == 1 &&
                    trace.events.front().subject == original &&
                    trace.declarationOrigins.empty(),
                "sequential trace reuse inherited a declaration origin");
      });
  cases.run("reused trace resets only at the outer service", [&] {
    auto source = fixture(context, "dot");
    RealizationTrace trace;
    {
      auto candidate = prepareProtocol(*source, false, {}, {}, &trace);
      require(bool(candidate), "first invocation failed");
    }
    auto count = trace.events.size();
    require(count && !events<ProposalDecision>(trace).empty() &&
                events<SelectionDecision>(trace).empty(),
            "preparation cleared trace or performed numerical selection");
    auto again = prepareProtocol(*source, false, {}, {}, &trace);
    require(bool(again) && trace.events.size() == count &&
                trace.events[0].sequence == 1 && trace.activeScopes.empty(),
            "trace accumulated a prior invocation");
    auto pubs = events<PublicationDecision>(trace);
    require(!pubs.empty() &&
                std::get<PublicationDecision>(pubs.back()->payload).boundary ==
                    PublicationBoundary::ReturnedCandidate,
            "standalone rewrite claimed installation");
    auto installed = copy(*source);
    PassManager manager(&context);
    manager.addPass(protocol::createPrepareProtocolPass(true, {}, &trace));
    require(succeeded(manager.run(*installed)), "PreparePass failed");
    pubs = events<PublicationDecision>(trace);
    require(std::get<PublicationDecision>(pubs.back()->payload).boundary ==
                    PublicationBoundary::PublishedToCaller &&
                pubs.back()->service == "prepare-pass",
            "caller publication did not occur at PreparePass installation");
  });
  for (bool bulk : {false, true})
    for (bool fusion : {false, true})
      for (bool simplify : {false, true})
        cases.run(
            "diagnostic modes preserve preparation " + std::to_string(bulk) +
                std::to_string(fusion) + std::to_string(simplify),
            [&, bulk, fusion, simplify] {
              auto source = fixture(context, "dot");
              auto control = prepareProtocol(*source, simplify, {bulk, fusion});
              require(bool(control), "preparation control failed");
              RealizationWork recorded;
              for (unsigned mode = 0; mode != 3; ++mode) {
                RealizationTrace trace;
                std::string text;
                llvm::raw_string_ostream stream(text);
                trace.remarks = mode == 1;
                trace.ir = mode == 2 ? &stream : nullptr;
                ScopedDiagnosticHandler quiet(
                    &context, [](Diagnostic &) { return success(); });
                auto candidate = prepareProtocol(*source, simplify,
                                                 {bulk, fusion}, {}, &trace);
                require(bool(candidate) && same(*control, *candidate),
                        "diagnostics changed prepared IR");
                if (mode)
                  require(sameWork(recorded, trace.remainingWork),
                          "diagnostics changed work");
                recorded = trace.remainingWork;
                if (mode == 2)
                  require(text.find("mathematical decision") !=
                              std::string::npos,
                          "dump omitted typed decisions");
              }
            });
  cases.run("participant demand lowering exposes its own publication", [&] {
    auto source = fixture(context, "total-collect");
    PassManager project(&context);
    project.addPass(protocol::createProjectProtocolPass());
    require(succeeded(project.run(*source)), "projection failed");
    auto control = copy(*source);
    PassManager baseline(&context);
    baseline.addPass(protocol::createLowerMathPass());
    require(succeeded(baseline.run(*control)), "demand control failed");
    RealizationTrace trace;
    PassManager observed(&context);
    observed.addPass(protocol::createLowerMathPass({}, &trace));
    require(succeeded(observed.run(*source)) && same(*source, *control),
            "demand observer changed lowering");
    auto publications = events<PublicationDecision>(trace);
    require(!publications.empty() &&
                publications.back()->service == "lower-math" &&
                std::get<PublicationDecision>(publications.back()->payload)
                        .boundary == PublicationBoundary::PublishedToCaller,
            "demand lowering masqueraded as preparation");
    require(events<SelectionDecision>(trace).empty(),
            "logical formation performed numerical selection");
    auto logical = copy(*source);
    require(succeeded(kernel::lowerKernels(*source, {}, &trace)) &&
                succeeded(kernel::verifyKernelLowering(*logical, *source)),
            "observed Kernel realization failed");
    bool expression = false;
    for (auto *event : events<SelectionDecision>(trace))
      expression |= event->service == "finite-expression";
    require(expression,
            "total finite selection missing from Kernel realization");
  });
  cases.run("nested occurrence state is independent of diagnostics", [&] {
    auto source = fixture(context, "nested-matrix"), before = copy(*source);
    RealizationTrace trace;
    std::string text;
    llvm::raw_string_ostream stream(text);
    trace.remarks = true;
    trace.ir = &stream;
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    RealizationWork wa, wb;
    auto control = prepare(*source, wa),
         observed = prepare(*source, wb, {}, &trace);
    require(control && observed && same(*control, *observed) &&
                same(*source, *before) && sameWork(wa, wb),
            "nested observation changed selection or its source");
    bool selected = false;
    for (auto *event : events<SelectionDecision>(trace))
      selected |= std::get<SelectionDecision>(event->payload).choice ==
                  RealizationChoice::NestedContraction;
    require(selected && trace.activeScopes.empty() &&
                trace.declarationOrigins.empty() &&
                sameWork(trace.remainingWork, wb),
            "nested selection was not observable or retained observer state");
  });
  return cases.result();
}
