#include "../lib/Transforms/Computation/Support.h"
#include "../lib/Transforms/FinitePreparation.h"
#include "../lib/Transforms/HelperNormalization.h"
#include "../lib/Transforms/MathematicalSupport.h"
#include "../lib/Transforms/RealizationTrace.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/ComputationRecipes.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/MathematicalTrace.h"
#include <algorithm>
#include <limits>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
using namespace zkc::mathematical;
namespace {
// Isolated Kernel recipe fixture: both fold results remain live when
// emit() copies two occurrences into its public standard-function entry. The
// retained pure helpers are the reader's source, independent of the producer's
// private selection view.
std::string fixtureText(unsigned width = 0, bool callFree = false,
                        unsigned depth = 0) {
  std::string text;
  llvm::raw_string_ostream out(text);
  out << R"mlir(
!F = !algebra.field<"koala-bear">
!V = !algebra.field_vector<"koala-bear">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 func.func private @multiply(%a:!F,%b:!F)->!F {
)mlir";
  auto unused = [&] {
    for (unsigned i = 0; i < width; ++i)
      out << "%unused" << i << " = algebra.field_add %a,%b : (!F,!F)->!F\n";
  };
  if (!callFree)
    unused();
  out << "%r = algebra.field_multiply %a,%b : (!F,!F)->!F\n"
         "func.return %r : !F\n}\n";
  std::string callee = "multiply";
  for (unsigned i = 0; i < depth; ++i) {
    auto name = "double_" + std::to_string(i);
    out << "func.func private @" << name << "(%a:!F,%b:!F)->!F {\n"
        << "%first = func.call @" << callee << "(%a,%b) : (!F,!F)->!F\n"
        << "%second = func.call @" << callee << "(%a,%b) : (!F,!F)->!F\n"
        << "func.return %second : !F\n}\n";
    callee = name;
  }
  out << "func.func private @step(%a:!F,%b:!F,%xs:!V)->!F {\n";
  if (callFree) {
    unused();
    out << "%r = algebra.field_multiply %a,%b : (!F,!F)->!F\n";
  } else {
    out << "%r = func.call @" << callee << "(%a,%b) : (!F,!F)->!F\n";
  }
  out << R"mlir(
   func.return %r : !F
 }
 func.func private @small_step(%a:!F,%b:!F,%xs:!V)->!F {
   %r = algebra.field_multiply %a,%b : (!F,!F)->!F
   func.return %r : !F
 }
 func.func private @total(%xs:!V,%seed:!F)->!F {
   %r = "algebra.finite_fold"(%xs,%seed) {domain=@items,step=@step} : (!V,!F)->!F
   func.return %r : !F
 }
 func.func private @small_total(%xs:!V,%seed:!F)->!F {
   %r = "algebra.finite_fold"(%xs,%seed) {domain=@items,step=@small_step} : (!V,!F)->!F
   func.return %r : !F
 }
 "protocol.func"() ({ ^entry(%xs:!V,%seed:!F):
   %r = func.call @total(%xs,%seed) : (!V,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
  return text;
}
protocol_ir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
func::FuncOp helper(ModuleOp module, StringRef name) {
  return SymbolTable(unit(module)).lookup<func::FuncOp>(name);
}
OwningOpRef<ModuleOp> fixture(MLIRContext &context, unsigned width = 0,
                              bool callFree = false, unsigned depth = 0) {
  auto result = parseSourceString<ModuleOp>(fixtureText(width, callFree, depth),
                                            &context);
  require(bool(result) && succeeded(verify(*result)), "fixture refused");
  return result;
}
bool same(Operation *left, Operation *right) {
  return OperationEquivalence::isEquivalentTo(
      left, right, OperationEquivalence::IgnoreLocations);
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
         a.discardedRecipeSiteBytes == b.discardedRecipeSiteBytes;
}
finite::Computation computationFixture(ModuleOp source) {
  finite::Computation result;
  require(succeeded(finite::describe(&helper(source, "total").front().front(),
                                     result, unit(source))),
          "missing computation");
  return result;
}
bool hasLoop(ModuleOp module) {
  bool found = false;
  module.walk([&](exec::RangeOp) { found = true; });
  return found;
}
OwningOpRef<ModuleOp> emit(ModuleOp source, RealizationWork &work,
                           RealizationTrace *trace = nullptr,
                           ArrayRef<StringRef> totals = {"total"},
                           bool optimize = true,
                           finite::VerificationLimits limits = {}) {
  auto numerical = computationRecipeUnit(unit(source));
  auto prototype = helper(source, "total");
  SmallVector<Type> results(totals.size(), prototype.getResultTypes().front());
  OpBuilder builder(source.getContext());
  builder.setInsertionPointToEnd(numerical->getBody());
  auto function = func::FuncOp::create(
      builder, source.getLoc(), "selected",
      builder.getFunctionType(prototype.getArgumentTypes(), results));
  function.setPublic();
  builder.setInsertionPointToEnd(function.addEntryBlock());
  SmallVector<Value> values;
  for (auto name : totals) {
    auto total = helper(source, name);
    IRMapping mapping;
    mapping.map(total.getArguments(), function.getArguments());
    auto *occurrence = builder.clone(total.front().front(), mapping);
    values.push_back(occurrence->getResult(0));
  }
  func::ReturnOp::create(builder, source.getLoc(), values);
  OwningOpRef<mlir::ModuleOp> original(
      cast<mlir::ModuleOp>(numerical->clone()));
  auto candidate = realizeComputationEntry(
      *numerical, "selection", {optimize, false}, work, limits, trace);
  require(bool(candidate), "checked callback lowering failed");
  computationRecipeOutput(*candidate);
  require(succeeded(computation::verifyRecipeOutput(*candidate)),
          "candidate refused");
  require(same(*numerical, *original), "Kernel recipe source changed");
  for (auto original : unit(source).getBody().front().getOps<func::FuncOp>())
    require(
        same(original, SymbolTable(*numerical).lookup(original.getSymName())),
        "source helper changed");
  return candidate;
}
const SelectionDecision &decision(const RealizationTrace &trace,
                                  unsigned ordinal) {
  for (const auto &event : trace.events)
    if (auto *selection = std::get_if<SelectionDecision>(&event.payload);
        selection && selection->family == DecisionFamily::Finite &&
        selection->querySubject.site ==
            computationRecipeSite("selection", ordinal))
      return *selection;
  throw std::runtime_error("missing selection at " + std::to_string(ordinal));
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run("sizing counts erased calls, slots, root and terminator", [&] {
    auto source = fixture(context);
    auto c = computationFixture(*source);
    uint64_t work = 100000;
    OptimizationOutcome outcome;
    auto size =
        finite::sizeCallbackPreparation(c, unit(*source), work, outcome);
    // Two four-unit operations are copied (call and multiply); the root and
    // return cost three, the admission scan costs one, and the private context
    // ten. No array projections means no projection-fold scans.
    require(size && size->work == 22 && !size->arrayProjections &&
                work == 99980,
            "incorrect preparation or scan cost");
    auto step = helper(*source, "step");
    OpBuilder builder(&step.front().back());
    builder.clone(step.front().front());
    require(succeeded(verify(*source)), "duplicate-call fixture refused");
    work = 100000;
    size = finite::sizeCallbackPreparation(c, unit(*source), work, outcome);
    require(size && size->work == 31 && !size->arrayProjections &&
                work == 99975,
            "duplicate call was not counted or shared callee was rescanned");
  });
  cases.run("an exhausted sizing invocation cannot poison later sizing", [&] {
    auto source = fixture(context);
    auto c = computationFixture(*source);
    uint64_t work = 10;
    OptimizationOutcome outcome;
    require(!finite::sizeCallbackPreparation(c, unit(*source), work, outcome) &&
                !work && outcome.status == OptimizationStatus::Capacity,
            "partial sizing did not retain its failed scan charge");
    work = 100000;
    auto size =
        finite::sizeCallbackPreparation(c, unit(*source), work, outcome);
    require(size && size->work == 22 && work == 99980,
            "temporary exhaustion was cached as a helper property");
  });
  cases.run("projection preparation follows nested helper bodies", [&] {
    auto text = fixtureText();
    text.insert(text.find("%r = algebra.field_multiply"), R"mlir(
 %pack = "algebra.array_from_elements"(%a,%b) : (!F,!F)->!algebra.field_array<"koala-bear",2>
 %selected = "algebra.array_at"(%pack) {index=1:i64} : (!algebra.field_array<"koala-bear",2>)->!F
)mlir");
    auto source = parseSourceString<ModuleOp>(text, &context);
    require(bool(source) && succeeded(verify(*source)),
            "packed helper refused");
    uint64_t work = 100000;
    OptimizationOutcome outcome;
    auto size = finite::sizeCallbackPreparation(computationFixture(*source),
                                                unit(*source), work, outcome);
    require(size && size->arrayProjections && size->work == 39,
            "nested projection folding was omitted from preparation work");
  });
  for (unsigned depth : {0u, 4u, 8u, 12u})
    cases.run("bounded doubling DAG " + llvm::Twine(depth), [&] {
      auto source = fixture(context, 0, false, depth);
      uint64_t work = std::numeric_limits<uint64_t>::max();
      const uint64_t initial = work;
      OptimizationOutcome outcome;
      auto size = finite::sizeCallbackPreparation(computationFixture(*source),
                                                  unit(*source), work, outcome);
      // Every edge contributes a fresh copy, but only one body is inspected
      // per helper. 13 * 2^depth + 9 includes intermediate calls and overhead.
      const uint64_t expected = std::min<uint64_t>(
          13 * (uint64_t(1) << depth) + 9, finite::callbackStructuralLimit + 1);
      require(size && size->work == expected &&
                  initial - work <= 20 + 15 * depth,
              "DAG multiplicity, saturation or memoized scan bound changed");
    });
  for (bool warm : {false, true})
    for (unsigned depth : {61u, 62u, 63u})
      cases.run("linear helper depth " + llvm::Twine(depth) +
                    (warm ? " memoized" : " fresh"),
                [&] {
                  auto text = fixtureText(0, false, depth);
                  // A linear chain reaches the depth boundary without exceeding
                  // admitted expansion size. Warm the leaf memo through a
                  // separate direct call.
                  size_t start = 0;
                  while ((start = text.find("%first = func.call", start)) !=
                         std::string::npos)
                    text.erase(start, text.find('\n', start) - start + 1);
                  start = text.find("func.func private @step");
                  start = text.find('{', start) + 1;
                  if (warm)
                    text.insert(
                        start,
                        "\n%warm = func.call @multiply(%a,%b) : (!F,!F)->!F\n");
                  // Formation rejects the over-limit case too. Parse it only
                  // to exercise this private defensive guard directly.
                  auto source = parseSourceString<ModuleOp>(
                      text, ParserConfig(&context, false));
                  require(bool(source), "linear depth fixture refused");
                  if (depth < 63)
                    require(succeeded(verify(*source)),
                            "in-range helper chain is not admitted");
                  uint64_t remaining = 100000;
                  OptimizationOutcome outcome;
                  auto size = finite::sizeCallbackPreparation(
                      computationFixture(*source), unit(*source), remaining,
                      outcome);
                  require(bool(size) == (depth < 63),
                          "memoized helper depth boundary changed");
                  if (!size)
                    require(outcome.reason == OptimizationReason::Depth,
                            "depth decline lost its cause");
                });
  cases.run("equation allowance stays shared across prepared callbacks", [&] {
    auto source = fixture(context);
    RealizationWork measured;
    auto reference = emit(*source, measured);
    const uint64_t spent = 100000 - measured.matching.equations;
    require(spent > 0 && !hasLoop(*reference), "equation measurement failed");
    RealizationWork work;
    work.matching.equations = spent;
    RealizationTrace trace;
    auto candidate = emit(*source, work, &trace, {"total", "small_total"});
    require(decision(trace, 0).choice == RealizationChoice::Reduction &&
                decision(trace, 1).choice == RealizationChoice::Ordered &&
                !work.matching.equations,
            "callback envelope refilled shared equation work");
  });
  for (uint64_t shared :
       {finite::callbackStructuralLimit - 1, finite::callbackStructuralLimit,
        finite::callbackStructuralLimit + 1})
    cases.run("exact envelope boundary " + llvm::Twine(shared), [&] {
      finite::ComputationWork work;
      work.structural = shared;
      OptimizationOutcome outcome = OptimizationOutcome::success();
      bool accepted;
      {
        finite::CallbackStructuralWork callback(work, outcome);
        accepted = finite::consumeComputationWork(
            callback.remaining.structural, finite::callbackStructuralLimit,
            WorkOwner::Structural, &outcome);
      }
      require(accepted == (shared >= finite::callbackStructuralLimit) &&
                  work.structural ==
                      (shared > finite::callbackStructuralLimit ? 1 : 0),
              "exact final-unit use was rejected or refunded");
      require(accepted ? outcome.status == OptimizationStatus::Succeeded
                       : outcome.capacity &&
                             outcome.capacity->owner == WorkOwner::Structural,
              "shared failure was attributed to the callback cap");
    });
  cases.run("local exhaustion retains all work and identifies its owner", [&] {
    finite::ComputationWork work;
    OptimizationOutcome outcome;
    {
      finite::CallbackStructuralWork callback(work, outcome);
      require(finite::consumeComputationWork(callback.remaining.structural,
                                             finite::callbackStructuralLimit),
              "could not spend the exact local allowance");
      require(!finite::consumeComputationWork(callback.remaining.structural, 1,
                                              WorkOwner::Structural, &outcome),
              "local cap was refilled");
      --callback.remaining.equations;
      --callback.remaining.evidence;
    }
    require(work.structural == 100000 - finite::callbackStructuralLimit &&
                work.equations == 99999 && work.evidence == 99999 &&
                outcome.capacity &&
                outcome.capacity->owner ==
                    WorkOwner::FiniteCallbackStructural &&
                outcome.capacity->requested == 1 &&
                outcome.capacity->available == 0,
            "scope refunded work or reported shared exhaustion");
    require(StringRef(decisionName(WorkOwner::FiniteCallbackStructural)) ==
                    "finite-callback-structural" &&
                StringRef(decisionName(OptimizationReason::ExpansionSize)) ==
                    "expansion-size",
            "missing diagnostic spelling");
  });
  for (bool reverse : {false, true})
    for (unsigned width : {2500u, 3000u, 9000u})
      cases.run(
          "structural opportunity after a wide callback " + llvm::Twine(width) +
              (reverse ? " reversed" : " forward"),
          [&] {
            auto source = fixture(context, width, width != 2500);
            RealizationWork work;
            work.matching.structural = 9000;
            RealizationTrace trace;
            SmallVector<StringRef> order =
                reverse ? SmallVector<StringRef>{"small_total", "total"}
                        : SmallVector<StringRef>{"total", "small_total"};
            auto candidate = emit(*source, work, &trace, order);
            const auto &large = decision(trace, reverse ? 1 : 0);
            const auto &small = decision(trace, reverse ? 0 : 1);
            require(large.choice == RealizationChoice::Ordered &&
                        large.outcome.status == OptimizationStatus::Capacity &&
                        large.outcome.capacity &&
                        large.outcome.capacity->owner ==
                            WorkOwner::FiniteCallbackStructural &&
                        small.choice == RealizationChoice::Reduction &&
                        work.matching.structural > 0 && hasLoop(*candidate),
                    "one callback consumed the later structural opportunity");
          });
  cases.run(
      "early DAG decline charges discovery without hypothetical copies", [&] {
        auto source = fixture(context, 0, false, 12);
        auto c = computationFixture(*source);
        uint64_t sizing =
            finite::callbackStructuralLimit - 1; // Root call discovery.
        OptimizationOutcome outcome;
        auto size =
            finite::sizeCallbackPreparation(c, unit(*source), sizing, outcome);
        require(size && size->work == finite::callbackStructuralLimit + 1,
                "DAG did not saturate");
        RealizationWork work;
        RealizationTrace trace;
        auto candidate = emit(*source, work, &trace, {"total", "small_total"});
        const auto &decline = decision(trace, 0);
        require(
            decline.outcome.reason == OptimizationReason::ExpansionSize &&
                decline.outcome.capacity &&
                !decline.outcome.capacity->requested &&
                decline.outcome.capacity->available == sizing &&
                decision(trace, 1).choice == RealizationChoice::Reduction,
            "early decline misreported its estimate or starved a small fold");
        RealizationWork smallWork;
        auto small = emit(*source, smallWork, nullptr, {"small_total"});
        require(
            work.matching.structural ==
                smallWork.matching.structural -
                    (finite::callbackStructuralLimit - sizing),
            "early decline debited hypothetical copies or refunded discovery");
      });
  cases.run("early shared-size decline preserves unspent work", [&] {
    auto source = fixture(context);
    RealizationWork work;
    work.matching.structural = 42; // Discovery 1, sizing 20, preparation 22.
    RealizationTrace trace;
    auto candidate = emit(*source, work, &trace);
    const auto &decline = decision(trace, 0);
    require(hasLoop(*candidate) && work.matching.structural == 21 &&
                decline.outcome.reason == OptimizationReason::ExpansionSize &&
                decline.outcome.capacity &&
                decline.outcome.capacity->owner == WorkOwner::Structural &&
                decline.outcome.capacity->requested == 22 &&
                decline.outcome.capacity->available == 21,
            "size prediction was reported as an actual shared debit");
  });
  cases.run("exact selection budget and repeated attempts retain debits", [&] {
    auto source = fixture(context);
    RealizationWork measured;
    auto reference = emit(*source, measured);
    require(!hasLoop(*reference), "measurement did not select");
    const uint64_t cost = 100000 - measured.matching.structural;
    for (uint64_t capacity : {cost - 1, cost, cost + 1}) {
      RealizationWork work;
      work.matching.structural = capacity;
      RealizationTrace trace;
      auto candidate = emit(*source, work, &trace);
      require(hasLoop(*candidate) == (capacity < cost) &&
                  work.matching.structural == (capacity > cost ? 1 : 0),
              "selection changed at an exact shared boundary");
      if (capacity < cost) {
        const auto &decline = decision(trace, 0);
        require(decline.outcome.reason == OptimizationReason::Work &&
                    decline.outcome.capacity &&
                    decline.outcome.capacity->owner == WorkOwner::Structural,
                "late shared exhaustion was reported as a size prediction");
      }
      auto repeated = emit(*source, work);
      require(hasLoop(*repeated) && !work.matching.structural,
              "repeated callback replenished work");
    }
  });
  for (unsigned depth : {4u, 12u})
    cases.run("tracing leaves IR and work unchanged " + llvm::Twine(depth),
              [&] {
                auto source = fixture(context, 0, false, depth);
                RealizationWork untraced, traced;
                RealizationTrace trace;
                auto first = emit(*source, untraced);
                auto second = emit(*source, traced, &trace);
                require(same(*first, *second) && sameWork(untraced, traced) &&
                            sameWork(traced, trace.remainingWork),
                        "tracing changed work or output");
              });
  cases.run(
      "comparison retry retains optional work and required reserves", [&] {
        auto original = fixture(context);
        RealizationWork work, orderedWork;
        auto source =
            emit(*original, work, nullptr, {"total"}, true, {100000, 1});
        auto ordered = emit(*original, orderedWork, nullptr, {"total"}, false);
        require(same(*source, *ordered),
                "comparison exhaustion did not retry ordered");
        require(work.matching.structural < orderedWork.matching.structural &&
                    work.helperOperations == orderedWork.helperOperations &&
                    work.helperSlots == orderedWork.helperSlots &&
                    work.polynomial == orderedWork.polynomial,
                "retry refunded optional work or altered required accounting");
      });
  for (bool throughCall : {false, true})
    cases.run(
        throughCall ? "callee nested finite keeps admission before expansion"
                    : "root nested finite keeps admission before expansion",
        [&] {
          auto source = fixture(context);
          auto step = helper(*source, "step");
          if (throughCall) {
            OpBuilder copyBuilder(step);
            auto nested = cast<func::FuncOp>(copyBuilder.clone(*step));
            nested.setSymName("nested_step");
            step.front().front().setAttr(
                "callee", FlatSymbolRefAttr::get(&context, "nested_step"));
            step.front().front().setOperands(step.getArguments());
            step = nested;
          }
          auto total = helper(*source, "small_total");
          IRMapping mapping;
          mapping.map(total.getArgument(0), step.getArgument(2));
          mapping.map(total.getArgument(1), step.getArgument(0));
          OpBuilder builder(&step.front().front());
          builder.clone(total.front().front(), mapping);
          require(succeeded(verify(*source)), "nested source refused");
          CheckedHelperNormalizations helpers(unit(*source));
          require(succeeded(helpers.prepare(step)),
                  "nested realization normalization refused");
          auto prepared = helpers.lookup(step);
          require(llvm::any_of(
                      prepared.front(),
                      [](Operation &op) { return finite::isComputation(&op); }),
                  "normalization erased unused nested admission");
          uint64_t structural = 100000;
          OptimizationOutcome outcome;
          require(!finite::sizeCallbackPreparation(computationFixture(*source),
                                                   unit(*source), structural,
                                                   outcome) &&
                      outcome.reason ==
                          OptimizationReason::ImplementationRestriction &&
                      structural == (throughCall ? 99982 : 99992),
                  "nested admission was sized as freely expandable work");
          RealizationWork work;
          RealizationTrace trace;
          auto candidate = emit(*source, work, &trace);
          require(decision(trace, 0).outcome.reason ==
                      OptimizationReason::ImplementationRestriction,
                  "nested restriction lost its reason");
          bool retained = false;
          candidate->walk([&](exec::ApplyOp op) {
            auto binding = dyn_cast_or_null<runtime::BindingOp>(
                SymbolTable::lookupNearestSymbolFrom(op, op.getBindingAttr()));
            retained |=
                binding && binding.getContract() == "vector.product" &&
                op->getParentOfType<func::FuncOp>()->hasAttr("runtime.region");
          });
          require(retained, "unused nested conditional admission disappeared");
        });
  cases.run("disabled selection skips discovery and sizing", [&] {
    auto source = fixture(context);
    RealizationWork work;
    auto candidate = emit(*source, work, nullptr, {"total"}, false);
    require(hasLoop(*candidate) && work.matching.structural == 100000,
            "disabled selection spent preparation work");
  });
  return cases.result();
}
