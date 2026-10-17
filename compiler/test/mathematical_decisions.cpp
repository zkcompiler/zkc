#include "../lib/Transforms/AlgorithmSupport.h"
#include "../lib/Transforms/Kernel/Support.h"
#include "../lib/Transforms/LaneRealization.h"
#include "../lib/Transforms/MathematicalSupport.h"
#include "../lib/Transforms/RecipeRealizations.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/Computation.h"
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
local::FuncOp calculation(ModuleOp module) {
  return SymbolTable(unit(module)).lookup<local::FuncOp>("calculation");
}
void outlineTotal(ModuleOp module) {
  auto total = SymbolTable(unit(module)).lookup<func::FuncOp>("total");
  require(bool(total), "missing total helper");
  OpBuilder builder(total);
  auto function = local::FuncOp::create(builder, total.getLoc(), "calculation",
                                        total.getFunctionType());
  function->setAttr("logical_origin",
                    builder.getArrayAttr({builder.getStringAttr("calculation"),
                                          builder.getArrayAttr({})}));
  builder.setInsertionPointToEnd(function.addEntryBlock());
  IRMapping mapping;
  mapping.map(total.getArguments(), function.getArguments());
  unsigned ordinal = 0;
  for (auto &operation : total.front().without_terminator()) {
    auto *copy = builder.clone(operation, mapping);
    copy->setAttr("site", builder.getStringAttr("calculation_" +
                                                std::to_string(ordinal++)));
  }
  SmallVector<Value> outputs;
  for (auto value : total.front().back().getOperands())
    outputs.push_back(mapping.lookup(value));
  local::ReturnOp::create(builder, total.getLoc(), outputs);
}
constexpr llvm::StringLiteral fusionFixture =
    R"mlir(!F = !algebra.field<"koala-bear">
!V = !algebra.field_vector<"koala-bear">
module { "protocol.module"() ({
 "local.binding"() {sym_name="sum",contract="vector.sum",arguments=["koala-bear"],implementation=""} : ()->()
 "local.binding"() {sym_name="length_alias",contract="vector.length",arguments=["koala-bear"],implementation=""} : ()->()
 "local.binding"() {sym_name="constant",contract="field.constant",arguments=["koala-bear"],implementation=""} : ()->()
 func.func private @formula(%a:!F,%b:!F,%unused:!F,%s:!F)->!F {
   %dead = "algebra.field_add"(%s,%s) : (!F,!F)->!F
   %p = "algebra.field_multiply"(%a,%b) : (!F,!F)->!F
   func.return %p : !F
 }
 algebra.map_realize @mapped = @formula [true, true, true, false] : (!V,!V,!V,!F)->!V
 local.func @reduce(%v:!V)->!F attributes {logical_origin=["reduce",[]]} {
   %r = "algebra.exec.vector_sum"(%v) {binding=@sum,parameters=[],site="sum"} : (!V)->!F
   local.return %r : !F
 }
 local.func @work(%a:!V,%b:!V,%c:!V,%s:!F)->!F attributes {logical_origin=["work",[]]} {
   %v = local.apply @mapped(%a,%b,%c,%s) {site="map"} : (!V,!V,!V,!F)->!V
   %r = local.apply @reduce(%v) {site="reduce"} : (!V)->!F
   local.return %r : !F
 }
 "protocol.func"() ({ ^entry(%a:!V,%b:!V,%c:!V,%s:!F):
   %r = "protocol.local_call"(%a,%b,%c,%s) {callee=@work,role="P",site="work"} : (!V,!V,!V,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!V,!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
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
         a.finiteExpressions == b.finiteExpressions;
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
  require(trace.policy.finiteBulk && !retry.effectivePolicy.finiteBulk,
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
  for (auto name : {"dot", "collect"})
    cases.run(std::string("finite retry ") + name, [&, name] {
      auto original = fixture(context, name);
      auto source = copy(*original), ordered = copy(*original),
           unobserved = copy(*original);
      RealizationWork work, orderedWork, unobservedWork;
      RealizationTrace trace;
      require(succeeded(finite::realizeLocals(*ordered, {false, false},
                                              &orderedWork)),
              "ordered control failed");
      require(succeeded(finite::realizeLocalsWithLimits(*source, {}, &work,
                                                        mathematicalRecipes(),
                                                        {100000, 1}, &trace)) &&
                  succeeded(finite::realizeLocalsWithLimits(
                      *unobserved, {}, &unobservedWork, mathematicalRecipes(),
                      {100000, 1})) &&
                  same(*source, *ordered) && same(*source, *unobserved) &&
                  sameWork(work, unobservedWork),
              "observation changed retry behavior or accounting");
      require(work.matching.equations < orderedWork.matching.equations &&
                  work.helperOperations == orderedWork.helperOperations &&
                  work.helperSlots == orderedWork.helperSlots,
              "retry replenished optional work or consumed required reserve");
      checkRetry(trace, "finite-attempt");
      auto publications = events<PublicationDecision>(trace);
      require(
          llvm::count_if(
              publications,
              [](const RealizationEvent *event) {
                return event->parent == 0 &&
                       std::get<PublicationDecision>(event->payload).boundary ==
                           PublicationBoundary::PublishedToCaller;
              }) == 1,
          "standalone finite service omitted caller installation");
      require(trace.activeScopes.empty() && sameWork(trace.remainingWork, work),
              "trace retained active scope or incorrect final balance");
    });
  cases.run("lane capacity retains ordered realization and typed decline", [&] {
    auto source = fixture(context, "collect"), ordered = copy(*source);
    RealizationTrace trace;
    RealizationWork work;
    work.lanes = 0;
    require(succeeded(finite::realizeLocals(*source, {}, &work, &trace)) &&
                succeeded(finite::realizeLocals(*ordered, {false, false})) &&
                same(*source, *ordered),
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
    auto unit = cast<protocol_ir::ProtocolModuleOp>(source->getBody()->front());
    auto declaration = SymbolTable(unit).lookup("collect");
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
    require(failed(finite::realizeLocalsWithLimits(*source, {}, nullptr,
                                                   mathematicalRecipes(),
                                                   {0, 100000}, &trace)) &&
                same(*source, *before),
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
  cases.run("later map failure invalidates earlier finite incorporation", [&] {
    auto source = fixture(context, "dot"),
         maps = fixture(context, "map-realization", true);
    auto unit = cast<protocol_ir::ProtocolModuleOp>(source->getBody()->front());
    auto mapUnit =
        cast<protocol_ir::ProtocolModuleOp>(maps->getBody()->front());
    OpBuilder builder(&unit.getBody().front(), unit.getBody().front().end());
    for (auto &op : mapUnit.getBody().front())
      if (isa<func::FuncOp, algebra::MapRealizeOp>(op))
        builder.clone(op);
    require(succeeded(verify(*source)), "combined admitted control refused");
    auto original = copy(*source);
    RealizationTrace trace;
    RealizationWork work;
    work.helperOperations = 0;
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    auto candidate = rewriteLocalAlgorithms(*source, {}, &trace, work);
    require(!candidate && same(*source, *original),
            "later required failure escaped atomically");
    uint64_t parent = 0;
    for (auto *event : events<DiscardDecision>(trace))
      if (event->service == "local-algorithms")
        parent = event->scope;
    bool incorporated = false, failedMap = false;
    for (auto *event : events<PublicationDecision>(trace)) {
      require(
          std::get<PublicationDecision>(event->payload).boundary ==
              PublicationBoundary::IncorporatedIntoParent,
          "failed preparation claimed a returned or caller-visible candidate");
      if (event->service == "finite-attempt")
        incorporated = true;
    }
    for (auto *event : events<DiscardDecision>(trace))
      if (event->service == "map-realizations") {
        auto *cause = std::get_if<RequiredFailure>(
            &std::get<DiscardDecision>(event->payload).cause);
        failedMap = event->parent == parent && cause && cause->capacity &&
                    cause->capacity->owner == WorkOwner::HelperOperations;
      }
    require(parent && incorporated && failedMap,
            "history omitted incorporation or parent refusal");
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
      outlineTotal(*source);
      auto original = copy(*source), ordered = copy(*source),
           unobserved = copy(*source);
      RealizationTrace trace;
      RealizationWork work, controlWork, orderedWork;
      require(
          succeeded(lowerCalculations(unit(*ordered), {calculation(*ordered)},
                                      {false, false}, &orderedWork)) &&
              succeeded(lowerCalculations(unit(*source), {calculation(*source)},
                                          {}, &work, {100000, 1}, &trace)) &&
              succeeded(lowerCalculations(unit(*unobserved),
                                          {calculation(*unobserved)}, {},
                                          &controlWork, {100000, 1})) &&
              same(*source, *ordered) && same(*source, *unobserved) &&
              sameWork(work, controlWork) &&
              succeeded(verifyCalculationRecipes(unit(*original), unit(*source),
                                                 {calculation(*source)})),
          "total retry changed IR, checking, or accounting");
      require(work.matching.structural < orderedWork.matching.structural,
              "total retry replenished matching work");
      checkRetry(trace, "calculation-attempt");
    });
  cases.run("reused trace resets only at the outer service", [&] {
    auto source = fixture(context, "dot");
    RealizationTrace trace;
    {
      auto candidate = rewriteLocalAlgorithms(*source, {}, &trace);
      require(bool(candidate), "first invocation failed");
    }
    auto count = trace.events.size();
    require(count && !events<SelectionDecision>(trace).empty(),
            "nested service cleared trace");
    auto again = rewriteLocalAlgorithms(*source, {}, &trace);
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
  cases.run("fusion recipes and occurrence choices are observational", [&] {
    auto source = parseSourceString<ModuleOp>(fusionFixture, &context);
    require(bool(source) && succeeded(verify(*source)),
            "fusion fixture refused");
    protocol::AlgorithmExpansionState state;
    require(succeeded(protocol::expandAlgorithms(
                *source, protocol::AlgorithmExpansionPhase::RetainMaps, state)),
            "retained fusion source failed");
    auto control = copy(*source), observed = copy(*source),
         missing = copy(*source);
    auto controlState = state, observedState = state, missingState = state;
    RealizationTrace trace;
    std::string text;
    llvm::raw_string_ostream stream(text);
    trace.remarks = true;
    trace.ir = &stream;
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    require(
        succeeded(fuseVectorReductions(*control, controlState)) &&
            succeeded(fuseVectorReductions(*observed, observedState, &trace)) &&
            same(*control, *observed),
        "fusion observer changed output");
    const auto &a = protocol::detail::AlgorithmStateAccess::get(controlState);
    const auto &b = protocol::detail::AlgorithmStateAccess::get(observedState);
    require(a == b, "fusion observer changed occurrence accounting");
    bool occurrence = false, product = false;
    for (auto *event : events<SelectionDecision>(trace)) {
      const auto &decision = std::get<SelectionDecision>(event->payload);
      product |= decision.family == DecisionFamily::MapProduct;
      occurrence |= decision.choice == RealizationChoice::MapSum &&
                    !event->subject.site.empty() &&
                    !event->subject.originalSite.empty();
    }
    require(product && occurrence,
            "fusion omitted formula or occurrence decision");
    require(succeeded(fuseVectorReductions(*missing, missingState,
                                           llvm::ArrayRef<ReductionRecipe>{},
                                           &trace)) &&
                same(*missing, *source),
            "missing optional recipe changed required map behavior");
    bool declined = false;
    for (auto *event : events<SelectionDecision>(trace))
      declined |= std::get<SelectionDecision>(event->payload).outcome.status ==
                      OptimizationStatus::MissingRecipe &&
                  !event->subject.site.empty();
    require(declined && events<PublicationDecision>(trace).empty(),
            "missing occurrence recipe was silent or claimed publication");
  });
  cases.run("wide fusion diagnostics preserve named occurrence identity", [&] {
    std::string text = fusionFixture.str(), calls;
    for (unsigned i = 0; i < 256; ++i)
      calls += " %unused" + std::to_string(i) +
               " = local.apply @mapped(%a,%b,%c,%s) {site=\"unused" +
               std::to_string(i) + "\"} : (!V,!V,!V,!F)->!V\n";
    text.insert(text.find(" %v = local.apply @mapped"), calls);
    auto source = parseSourceString<ModuleOp>(text, &context);
    require(bool(source) && succeeded(verify(*source)), "wide source refused");
    protocol::AlgorithmExpansionState state;
    RealizationTrace preparation;
    require(succeeded(protocol::expandAlgorithms(
                *source, protocol::AlgorithmExpansionPhase::RetainMaps, state,
                nullptr, &preparation)),
            "wide retained source refused");
    bool installed = false;
    for (auto *event : events<PublicationDecision>(preparation))
      installed |= event->parent == 0 &&
                   std::get<PublicationDecision>(event->payload).boundary ==
                       PublicationBoundary::PublishedToCaller;
    require(installed, "standalone expansion omitted caller installation");
    auto control = copy(*source), observed = copy(*source);
    auto controlState = state, observedState = state;
    RealizationTrace trace;
    require(
        succeeded(fuseVectorReductions(*control, controlState)) &&
            succeeded(fuseVectorReductions(*observed, observedState, &trace)) &&
            same(*control, *observed),
        "wide diagnostic changed fusion");
    unsigned declined = 0;
    for (auto *event : events<SelectionDecision>(trace)) {
      const auto &selection = std::get<SelectionDecision>(event->payload);
      if (selection.family != DecisionFamily::VectorReduction ||
          selection.choice != RealizationChoice::Ordered)
        continue;
      require(!event->subject.site.empty() && event->subject.position.empty() &&
                  event->subject.declaration == "work" &&
                  !event->subject.originalSite.empty(),
              "named occurrence lost its declaration or origin");
      ++declined;
    }
    require(declined >= 256, "wide nonfusing occurrences were omitted");
  });
  cases.run("positive origin allowance can fail at the encoding request", [&] {
    auto source = parseSourceString<ModuleOp>(fusionFixture, &context);
    require(bool(source), "fusion fixture refused");
    protocol::AlgorithmExpansionState state;
    require(succeeded(protocol::expandAlgorithms(
                *source, protocol::AlgorithmExpansionPhase::RetainMaps, state)),
            "retained source failed");
    auto record = protocol::detail::AlgorithmStateAccess::get(state);
    record.originBytes = 1;
    protocol::detail::AlgorithmStateAccess::set(state, record);
    auto before = copy(*source);
    RealizationTrace trace;
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    require(failed(fuseVectorReductions(*source, state, &trace)) &&
                same(*source, *before),
            "origin capacity published a partial rewrite");
    auto discards = events<DiscardDecision>(trace);
    require(discards.size() == 1, "origin capacity lost its proposal discard");
    const auto *cause = std::get_if<RequiredFailure>(
        &std::get<DiscardDecision>(discards[0]->payload).cause);
    require(
        cause && cause->capacity &&
            cause->capacity->owner == WorkOwner::AlgorithmOriginBytes &&
            cause->capacity->available == 1 && !cause->capacity->requested &&
            protocol::detail::AlgorithmStateAccess::get(state).originBytes == 1,
        "origin failure inferred zero balance, invented request size, or "
        "published state");
  });
  cases.run("nested occurrence state is independent of diagnostics", [&] {
    auto source = fixture(context, "nested-matrix");
    auto control = copy(*source), observed = copy(*source);
    protocol::AlgorithmExpansionState a, b;
    RealizationTrace trace;
    std::string text;
    llvm::raw_string_ostream stream(text);
    trace.remarks = true;
    trace.ir = &stream;
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    require(succeeded(protocol::expandAlgorithms(
                *control, protocol::AlgorithmExpansionPhase::RetainMaps, a)) &&
                succeeded(protocol::expandAlgorithms(
                    *observed, protocol::AlgorithmExpansionPhase::RetainMaps, b,
                    nullptr, &trace)),
            "retained expansion failed");
    RealizationWork wa, wb;
    require(succeeded(nested::rewriteFiniteCollections(*control, a, {}, &wa)) &&
                succeeded(nested::rewriteFiniteCollections(*observed, b, {},
                                                           &wb, &trace)) &&
                same(*control, *observed) && sameWork(wa, wb),
            "nested observation changed selection");
    const auto &ar = protocol::detail::AlgorithmStateAccess::get(a);
    const auto &br = protocol::detail::AlgorithmStateAccess::get(b);
    require(ar == br, "observer changed occurrence state");
    bool selected = false;
    for (auto *event : events<SelectionDecision>(trace))
      selected |= std::get<SelectionDecision>(event->payload).choice ==
                  RealizationChoice::NestedContraction;
    require(selected, "nested selection was not observable");
  });
  return cases.result();
}
