#include "../lib/Transforms/ComputationSelection.h"
#include "../lib/Transforms/FinitePreparation.h"
#include "../lib/Transforms/LaneRealization.h"
#include "../lib/Transforms/MathematicalRecipes.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "support/ScopedComputation.h"
#include "support/ScopedFinite.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Finite.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/raw_ostream.h"
#include <fstream>
#include <sstream>
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace sf = zkc::test::scopedFinite;
namespace sc = zkc::test::scopedComputation;
namespace {
const char *source = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : () -> ()
 "data.domain"() ({
 ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V) -> !data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>) -> ()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 func.func private @step(%scope:!runtime.scope,%state:!F,%item:!F,%xs:!V) -> !exec.outcome<(!F)> attributes {no_inline,runtime.origin=["step",[]]} {
   %next = "exec.apply"(%scope,%state,%item) {binding=@add,parameters=[],site="add"} : (!runtime.scope,!F,!F)->!exec.outcome<(!F)>
   "exec.dispatch"(%next)[^ok,^stop] : (!exec.outcome<(!F)>)->()
 ^ok(%value:!F):
   %result = "exec.returned"(%value) : (!F)->!exec.outcome<(!F)>
   func.return %result : !exec.outcome<(!F)>
 ^stop(%reason:!exec.stop):
   %failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(!F)>
   func.return %failure : !exec.outcome<(!F)>
 }
 func.func @work(%scope:!runtime.scope,%xs:!V,%init:!F) -> !exec.outcome<(!F)> attributes {no_inline,runtime.origin=["work",[]]} {
   %r = "exec.fold"(%scope,%xs,%init) {domain=@items,step=@step,site="fold"} : (!runtime.scope,!V,!F)->!exec.outcome<(!F)>
   "exec.dispatch"(%r)[^ok,^stop] : (!exec.outcome<(!F)>)->()
 ^ok(%value:!F):
   %result = "exec.returned"(%value) : (!F)->!exec.outcome<(!F)>
   func.return %result : !exec.outcome<(!F)>
 ^stop(%reason:!exec.stop):
   %failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(!F)>
   func.return %failure : !exec.outcome<(!F)>
 }
 "protocol.func"() ({
 ^entry(%xs:!V,%init:!F):
   %r = "protocol.local_call"(%xs,%init) {callee=@work,role="P",site="work"} : (!V,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
std::string replace(std::string text, StringRef old, StringRef next) {
  auto pos = text.find(old.str());
  require(pos != std::string::npos, "missing fixture edit");
  text.replace(pos, old.size(), next.str());
  return text;
}
} // namespace
std::string fixture(StringRef name) {
  std::ifstream stream(std::string(ZKC_FINITE_FIXTURES) + "/" + name.str() +
                       ".mlir");
  require(bool(stream), "missing finite fixture");
  std::ostringstream text;
  text << stream.rdbuf();
  return text.str();
}
// Construct the actual scoped callback. Recognition owns a separate, admitted
// mathematical view; none of these controls mutate that private view.
void linearBody(func::FuncOp helper, unsigned terms, StringRef binding,
                unsigned initial, unsigned repeated, bool subtract = false) {
  helper.getBody().dropAllReferences();
  helper.getBody().getBlocks().clear();
  OpBuilder builder(helper.getContext());
  builder.setInsertionPointToEnd(helper.addEntryBlock());
  exec::ScopedExecutionBuilder control(builder, helper);
  auto item = helper.getArgument(repeated);
  Value previous = helper.getArgument(initial);
  for (unsigned i = 0; i < terms; ++i) {
    auto values = control.invoke(
        "exec.apply", TypeRange{item.getType()},
        control.scoped(subtract ? ValueRange{item, previous}
                                : ValueRange{previous, item}),
        {builder.getNamedAttr(
             "binding", FlatSymbolRefAttr::get(helper.getContext(), binding)),
         builder.getNamedAttr("parameters", builder.getArrayAttr({})),
         builder.getNamedAttr(
             "site", builder.getStringAttr("term" + std::to_string(i)))});
    previous = values.front();
  }
  control.returned(previous);
}
OwningOpRef<ModuleOp> linearCollect(MLIRContext &context, unsigned additions,
                                    bool subtract = false) {
  auto module = parseSourceString<ModuleOp>(fixture("collect"), &context);
  require(bool(module), "collect fixture refused");
  auto binding = SymbolTable(&module->getBody()->front())
                     .lookup<runtime::BindingOp>("mul");
  binding.setContract(subtract ? "field.sub" : "field.add");
  linearBody(sf::function(*module, "square"), additions, "mul", 1, 1, subtract);
  require(succeeded(verify(*module)), "linear callback refused");
  return module;
}
OwningOpRef<ModuleOp> prepare(ModuleOp source,
                              mathematical::RealizationWork &work,
                              MathematicalSelectionPolicy policy = {}) {
  uint64_t copy = 1000000, bytes = 16 * 1024 * 1024;
  std::optional<CapacityCause> capacity;
  auto result = protocol::prepareScopedFinite(source, work, copy, bytes,
                                              capacity, policy);
  require(bool(result), "scoped finite preparation failed");
  require(succeeded(sf::compare(source, *result)),
          "independent scoped comparison failed");
  return result;
}
bool reached(ModuleOp module, StringRef name) {
  return !sf::executionApplications(module, "work", name).empty();
}
// Ring depth and scoped callback-analysis capacity are different limits. Read
// the actual callback with sufficient structural work before testing Ring's
// exact limit; the default emitter still applies its private callback envelope.
void checkLaneDepth(ModuleOp module, bool fits) {
  auto subject = readComputation(module);
  auto selected = mathematical::selectComputation(subject, {});
  require(selected.kind == mathematical::RealizationKind::Elementwise &&
              selected.view && selected.view->callbackBody,
          "linear callback has no mathematical view");
  auto &body = *selected.view->callbackBody;
  auto vector = body.getArgument(1);
  llvm::DenseMap<Value, mathematical::LaneInput> inputs;
  inputs[body.getArgument(0)] = {vector, true};
  inputs[vector] = {vector, false};
  uint64_t remaining = 1000000;
  auto admitted = take(
      mathematical::admitLaneFormula(body, inputs, vector.getType(), &remaining,
                                     mathematical::mathematicalRecipes()));
  require(fits ? bool(admitted.formula)
               : !admitted.formula &&
                     admitted.status ==
                         mathematical::LaneRealizationStatus::Capacity &&
                     admitted.reason == "ring-depth",
          "exact Ring depth boundary changed");
}
void refusesIR(StringRef text, MLIRContext &context, StringRef code) {
  SmallVector<std::string> codes;
  ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
    for (auto &refusal : diagnostics::refusals(diagnostic))
      codes.push_back(refusal.code);
    return success();
  });
  require(!parseSourceString<ModuleOp>(text, &context),
          "invalid IR was admitted");
  require(llvm::is_contained(codes, code.str()), "missing refusal identifier " +
                                                     code + "; observed " +
                                                     llvm::join(codes, ", "));
}
void pipeline(ModuleOp module, bool optimize = true) {
  PassManager pm(module.getContext());
  pm.addPass(protocol::createProjectProtocolPass(optimize, {optimize, false}));
  pm.addPass(protocol::createLowerMathPass({optimize, false}));
  pm.addPass(protocol::createSelectPhysicalPass());
  require(succeeded(pm.run(module)), "finite pipeline failed");
}
int main(int argc, char **argv) {
  bool checkedAccess = argc == 2 && StringRef(argv[1]) == "--checked-access";
  require(argc == 1 || checkedAccess, "expected optional --checked-access");
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  auto original = parseSourceString<ModuleOp>(source, &context);
  require(bool(original), "finite source refused");
  cases.run("repeated associative terms have linear recognition work", [&] {
    uint64_t smallerCost = 0;
    for (unsigned terms : {160u, 320u}) {
      auto module = parseSourceString<ModuleOp>(source, &context);
      require(bool(module), "fold fixture refused");
      linearBody(sf::function(*module, "step"), terms, "add", 1, 2);
      require(succeeded(verify(*module)), "long repeated-term fold refused");
      auto subject = readComputation(*module);
      auto later = readComputation(*original);
      auto view = finite::analyzeComputation(subject);
      require(bool(view), "long fold has no structural view");
      finite::ComputationWork shared;
      auto selected = mathematical::selectComputation(*view, {}, shared);
      auto cost = finite::ComputationWork{}.equations - shared.equations;
      require(
          selected.kind == mathematical::RealizationKind::PointwiseReduction &&
              selected.equations.pointwiseReduction->additionalTerms.size() ==
                  terms - 1 &&
              cost <= 32 * terms + 128,
          "spine classification rescanned its body or dropped repeated terms");
      auto repeated = selected.equations.pointwiseReduction->term;
      require(
          llvm::all_of(selected.equations.pointwiseReduction->additionalTerms,
                       [&](Value value) { return value == repeated; }),
          "repeated sibling occurrences were not retained");
      require(mathematical::selectComputation(later, {}, shared).kind ==
                  mathematical::RealizationKind::Reduction,
              "long spine starved a subsequent eligible fold");
      if (smallerCost)
        require(cost <= 2 * smallerCost + 128,
                "doubling spine length used superlinear equation work");
      smallerCost = cost;
      finite::ComputationWork exact;
      exact.equations = cost;
      require(mathematical::selectComputation(*view, {}, exact).kind ==
                      mathematical::RealizationKind::PointwiseReduction &&
                  !exact.equations,
              "exact spine recognition allowance was not consumed");
      exact.equations = cost - 1;
      auto declined = mathematical::selectComputation(*view, {}, exact);
      require(declined.kind == mathematical::RealizationKind::Ordered &&
                  declined.outcome() == OptimizationStatus::Capacity &&
                  !exact.equations,
              "short spine allowance did not retain ordered execution");
      mathematical::RealizationWork stageWork;
      auto candidate = prepare(*module, stageWork);
      require(!sf::hasLoop(*candidate) &&
                  (reached(*candidate, "numerical.sum") ||
                   reached(*candidate, "vector.sum")),
              "long repeated spine lost bulk selection");
      auto small = prepare(*original, stageWork);
      require(!sf::hasLoop(*small) && reached(*small, "vector.sum"),
              "long spine starved later stage selection");
    }
  });
  cases.run("lane outcomes distinguish decline from construction failure", [&] {
    auto module = parseSourceString<ModuleOp>(fixture("collect"), &context);
    require(bool(module), "collect was refused");
    SymbolTable symbols(&module->getBody()->front());
    auto subject = readComputation(*module);
    auto view = finite::analyzeComputation(subject);
    require(bool(view), "missing collect structural view");
    auto &body = *view->callbackBody;
    auto vector = body.getArgument(1);
    llvm::DenseMap<Value, mathematical::LaneInput> inputs;
    inputs[body.getArgument(0)] = {vector, true};
    inputs[vector] = {vector, false};
    unsigned emitted = 0;
    auto emit = [&](StringRef, ValueRange, Type, ArrayRef<std::string>) {
      ++emitted;
      return Value();
    };
    uint64_t remaining = 0;
    auto declined = take(mathematical::realizeLanes(
        body, inputs, vector.getType(), {}, &remaining,
        mathematical::mathematicalRecipes(), emit));
    require(declined.status == mathematical::LaneRealizationStatus::Capacity &&
                declined.reason == "mathematical-lane-work" && !emitted,
            "optional capacity emitted part of a candidate");
    remaining = 1000;
    auto work = symbols.lookup<func::FuncOp>("work");
    llvm::DenseMap<Value, mathematical::LaneInput> noInputs;
    auto unsupported = take(mathematical::realizeLanes(
        work.getBody().front(), noInputs, vector.getType(), {}, &remaining,
        mathematical::mathematicalRecipes(), emit));
    require(unsupported.status ==
                    mathematical::LaneRealizationStatus::Unsupported &&
                unsupported.reason == "mathematical-lane-unsupported" &&
                !emitted,
            "unsupported formula emitted part of a candidate");
    remaining = 1000;
    refuses(mathematical::realizeLanes(
                body, inputs, vector.getType(), {}, &remaining,
                mathematical::mathematicalRecipes(), emit),
            "mathematical-lane-realization");
    require(emitted == 1, "construction failure did not come from the emitter");
  });
  for (unsigned additions : {512u, 1023u, 1024u})
    cases.run("optional lane depth " + std::to_string(additions), [&] {
      for (bool prepareSource : {false, true}) {
        auto module = linearCollect(context, additions);
        if (prepareSource) {
          PassManager pm(&context);
          pm.addPass(protocol::createPrepareProtocolPass());
          require(succeeded(pm.run(*module)), "source preparation failed");
        }
        checkLaneDepth(*module, additions < 1024);
        if (additions >= 1023) {
          finite::ComputationWork shared;
          mathematical::ComputationSelection selected;
          auto subject = readComputation(*module);
          {
            finite::CallbackStructuralWork callback(
                shared, selected.diagnostic.outcome);
            selected = mathematical::selectComputation(subject, {},
                                                       callback.remaining);
          }
          require(selected.kind == mathematical::RealizationKind::Ordered &&
                      selected.outcome() == OptimizationStatus::Capacity &&
                      selected.diagnostic.outcome.capacity &&
                      selected.diagnostic.outcome.capacity->owner ==
                          WorkOwner::FiniteCallbackStructural &&
                      shared.structural ==
                          finite::ComputationWork{}.structural -
                              finite::callbackStructuralLimit,
                  "scoped callback limit lost its cause or shared debit");
        }
        auto candidate = sf::prepare(*module);
        require(succeeded(sf::compare(*module, *candidate)),
                "linear collection comparison failed");
        bool loop = sf::hasLoop(*candidate);
        bool lanes = reached(*candidate, "vector.add") ||
                     reached(*candidate, "numerical.map");
        require(
            loop == (additions >= 1023) && lanes == !loop,
            "scoped callback capacity did not select bulk or clean fallback");
      }
    });
  for (unsigned subtractions : {511u, 512u})
    cases.run(
        "right-nested subtraction depth " + std::to_string(subtractions), [&] {
          auto module = linearCollect(context, subtractions, true);
          checkLaneDepth(*module, subtractions == 511);
          auto candidate = sf::prepare(*module);
          require(succeeded(sf::compare(*module, *candidate)),
                  "subtraction collection comparison failed");
          bool loop = sf::hasLoop(*candidate);
          bool lanes = reached(*candidate, "vector.sub") ||
                       reached(*candidate, "numerical.map");
          require(loop == (subtractions == 512) && lanes == !loop,
                  "subtraction's extra negation depth lost clean fallback");
        });
  cases.run("lane work is shared across invocations", [&] {
    auto original = parseSourceString<ModuleOp>(fixture("collect"), &context);
    require(bool(original), "collect fixture refused");
    // Measure one invocation, then give two occurrences exactly that allowance.
    mathematical::RealizationWork measured;
    uint64_t initial = measured.lanes;
    auto single = prepare(*original, measured);
    auto cost = initial - measured.lanes;
    require(cost && !sf::hasLoop(*single), "missing lane-work control");
    auto helper = sf::function(*original, "work");
    exec::CollectOp collect;
    helper.walk([&](exec::CollectOp op) { collect = op; });
    require(bool(collect), "missing collection");
    auto second = sc::duplicateInvocation(collect, helper, "second");
    sc::returned(helper)->setOperand(0, sc::payload(second).front());
    require(succeeded(verify(*original)), "two invocations refused");
    for (uint64_t allowance : {uint64_t(0), cost}) {
      mathematical::RealizationWork work;
      work.lanes = allowance;
      auto candidate = prepare(*original, work);
      unsigned loops = 0;
      candidate->walk([&](exec::RangeOp) { ++loops; });
      auto lanes =
          sf::executionApplications(*candidate, "work", "vector.mul").size() +
          sf::executionApplications(*candidate, "work", "numerical.map").size();
      require(loops == (allowance ? 1u : 2u) && lanes == 2 - loops,
              "lane budget was reset or a declined candidate emitted payload");
      require(work.lanes == 0, "lane work was not charged to the caller");
    }
  });
  cases.run("bound queries share the enclosing work budget", [&] {
    auto module = parseSourceString<ModuleOp>(fixture("total-state"), &context);
    require(bool(module), "total-state source refused");
    bool checked = false;
    module->walk([&](data::BoundedAtOp access) {
      uint64_t remaining = 65536;
      require(finite::provesBound(access.getOperand(1), access.getOperand(0), 0,
                                  remaining),
              "known bound was lost");
      auto consumed = 65536 - remaining;
      require(consumed > 0, "bound query did not charge its enclosing budget");
      remaining = consumed;
      require(finite::provesBound(access.getOperand(1), access.getOperand(0), 0,
                                  remaining) &&
                  remaining == 0,
              "bound query charged inconsistently");
      require(!finite::provesBound(access.getOperand(1), access.getOperand(0),
                                   0, remaining),
              "exhausted bound query acquired a fresh budget");
      remaining = 1;
      require(finite::provesEqualExtent(access.getOperand(0), 0,
                                        access.getOperand(0), 0, remaining) &&
                  remaining == 0,
              "extent evidence did not consume shared work");
      require(!finite::provesEqualExtent(access.getOperand(0), 0,
                                         access.getOperand(0), 0, remaining),
              "exhausted extent query acquired a fresh budget");
      checked = true;
    });
    require(checked, "missing source bound access");
  });
  for (bool optimize : {false, true})
    cases.run(optimize ? "native sum" : "generic fold", [&] {
      auto candidate = sf::prepare(*original, {optimize, false});
      require(succeeded(sf::compare(*original, *candidate)),
              "independent correspondence failed");
      require(optimize ? reached(*candidate, "vector.sum")
                       : sf::hasLoop(*candidate),
              "required realization missing");
      auto root = sf::function(*candidate, "work");
      sc::returned(root)->setOperand(0, root.getArgument(2));
      require(succeeded(verify(*candidate)), "result mutation malformed");
      require(failed(sf::compare(*original, *candidate)),
              "mutated result accepted");
    });
  for (bool optimize : {false, true})
    cases.run(optimize ? "optimized pipeline" : "fallback pipeline", [&] {
      OwningOpRef<ModuleOp> candidate(cast<ModuleOp>((*original)->clone()));
      PassManager pm(&context);
      pm.addPass(
          protocol::createProjectProtocolPass(optimize, {optimize, false}));
      pm.addPass(protocol::createLowerMathPass({optimize, false}));
      pm.addPass(protocol::createSelectPhysicalPass());
      require(succeeded(pm.run(*candidate)), "finite pipeline failed");
    });
  for (bool simplify : {false, true})
    for (bool bulk : {false, true})
      cases.run(
          std::string("finite policy independent of simplify ") +
              (simplify ? "on/" : "off/") + (bulk ? "bulk" : "loop"),
          [&] {
            for (bool fuse : {false, true}) {
              MathematicalSelectionPolicy policy{bulk, fuse};
              OwningOpRef<ModuleOp> candidate(
                  cast<ModuleOp>((*original)->clone()));
              PassManager prepare(&context);
              prepare.addPass(
                  protocol::createPrepareProtocolPass(simplify, policy));
              require(succeeded(prepare.run(*candidate)),
                      "policy preparation failed");
              require(!sf::hasLoop(*candidate) &&
                          !reached(*candidate, "vector.sum"),
                      "source preparation selected executable work early");
              bool finiteRequest = false;
              candidate->walk([&](exec::FoldOp) { finiteRequest = true; });
              require(finiteRequest, "source preparation lost finite meaning");
              auto selected = sf::prepare(*candidate, policy);
              require(reached(*selected, "vector.sum") == bulk &&
                          sf::hasLoop(*selected) == !bulk,
                      "finite selection followed simplify or fusion");
              OwningOpRef<ModuleOp> projected(
                  cast<ModuleOp>((*candidate)->clone()));
              PassManager project(&context);
              project.addPass(
                  protocol::createProjectProtocolPass(simplify, policy));
              require(succeeded(project.run(*projected)),
                      "policy projection failed");
              require(succeeded(mathematical::verifyAuthoredLocalsPreserved(
                          &candidate->getBody()->front(),
                          &projected->getBody()->front())),
                      "projection changed accepted scoped definitions");
              auto total = parseSourceString<ModuleOp>(fixture("total-collect"),
                                                       &context);
              require(bool(total), "total fixture refused");
              PassManager demand(&context);
              demand.addPass(
                  protocol::createProjectProtocolPass(simplify, policy));
              demand.addPass(protocol::createLowerMathPass(policy));
              demand.addPass(protocol::createSelectPhysicalPass());
              require(succeeded(demand.run(*total)),
                      "total demand policy failed");
              bool totalLoop = false;
              total->walk([&](exec::RangeOp) { totalLoop = true; });
              require(totalLoop == !bulk,
                      "total demand ignored finite family policy");
            }
          });
  cases.run("default source preparation retains finite requests", [&] {
    auto candidate = mathematical::prepareProtocol(*original, false);
    require(bool(candidate), "checked source preparation failed");
    bool retained = false;
    candidate->walk([&](exec::FoldOp) { retained = true; });
    require(retained && !reached(*candidate, "vector.sum") &&
                !sf::hasLoop(*candidate),
            "source preparation changed the selection boundary");
    auto selected = sf::prepare(*candidate);
    require(reached(*selected, "vector.sum") && !sf::hasLoop(*selected),
            "default executable preparation omitted bulk selection");
  });
  cases.run("descriptor arbitrary expression refused", [&] {
    auto invalid = replace(
        source, "   %d =",
        "   %bad = \"data.index\"() {value=\"0\"} : () -> ui64\n   %d =");
    require(!parseSourceString<ModuleOp>(invalid, &context),
            "descriptor evaluated arbitrary expression");
  });
  cases.run("same helper name changed body refused", [&] {
    auto candidate = sf::prepare(*original);
    auto helper = sf::function(*candidate, "step");
    sc::returned(helper)->setOperand(0, helper.getArgument(1));
    require(succeeded(verify(*candidate)), "changed helper malformed");
    require(failed(sf::compare(*original, *candidate)),
            "stale helper accepted");
  });
  for (StringRef name : {"dot",
                         "collect",
                         "total-state",
                         "unit-state",
                         "affine",
                         "filter",
                         "predicate-stop",
                         "independent",
                         "dependent",
                         "stopping-branches",
                         "mixed-sequence",
                         "order",
                         "nested-total",
                         "total-collect",
                         "product",
                         "aliased-predicate",
                         "msm",
                         "materialized",
                         "match",
                         "dot-large",
                         "realized-total",
                         "fixed-collect",
                         "total-predicate",
                         "eager",
                         "coordinates-row",
                         "coordinates-column",
                         "total-zip",
                         "dead-domain",
                         "affine-successor"}) {
    for (bool optimize : {false, true})
      cases.run(name + (optimize ? " optimized" : " fallback"), [&] {
        auto module = parseSourceString<ModuleOp>(fixture(name), &context);
        require(bool(module), "finite fixture refused");
        pipeline(*module, optimize);
      });
  }
  for (StringRef name : {"matrix-row", "matrix-column"})
    cases.run(name + " optimized", [&] {
      auto module = parseSourceString<ModuleOp>(fixture(name), &context);
      require(bool(module), "matrix fixture refused");
      pipeline(*module);
    });
  for (bool optimize : {false, true})
    cases.run(
        optimize ? "bulk identity collect retains eager ignored capture"
                 : "ordered identity collect retains eager ignored capture",
        [&] {
          auto text = replace(
              fixture("total-collect"),
              "   %y = algebra.field_multiply %x,%factor : (!F,!F)->!F\n"
              "   %z = algebra.field_add %y,%factor : (!F,!F)->!F\n"
              "   func.return %z : !F",
              "   func.return %x : !F");
          text = replace(
              text, "   %r = \"algebra.finite_collect\"(%xs,%factor)",
              "   %capture = algebra.field_add %factor,%factor : (!F,!F)->!F\n"
              "   %r = \"algebra.finite_collect\"(%xs,%capture)");
          auto module = parseSourceString<ModuleOp>(text, &context);
          require(bool(module), "ignored capture fixture refused");
          PassManager lower(&context);
          lower.addPass(
              protocol::createProjectProtocolPass(optimize, {optimize, false}));
          lower.addPass(protocol::createLowerMathPass({optimize, false}));
          require(succeeded(lower.run(*module)),
                  "ignored capture lowering failed");
          PassManager physical(&context);
          physical.addPass(protocol::createSelectPhysicalPass());
          require(succeeded(physical.run(*module)),
                  "ignored capture physical selection failed");
          unsigned additions = sf::applications(*module, "field.add").size();
          require(additions == 1,
                  "eager capture calculation was removed or duplicated");
        });
  cases.run("finite repeated state fixed point and conservative cloning", [&] {
    auto module = parseSourceString<ModuleOp>(fixture("total-state"), &context);
    require(bool(module), "total fixture refused");
    Operation *fold = nullptr;
    module->walk([&](algebra::FiniteFoldOp op) { fold = op; });
    finite::Summary summary;
    require(succeeded(finite::summarize(fold, summary)), "summary failed");
    require(summary.results.size() == 2 && summary.results[0].test(0) &&
                summary.results[0].test(1) && summary.results[0].test(2),
            "state dependence did not reach a fixed point");
    auto dependencies = mathematical::operandDependencies(fold, 0);
    require(succeeded(dependencies) && dependencies->size() == 3,
            "whole operation cloning was narrowed");
  });
  cases.run("empty native state retains total formation", [&] {
    auto text = replace(fixture("total-state"),
                        "@step(%a:!F,%b:!F,%i:ui64,%xs:!V) -> (!F,!F)",
                        "@step(%i:ui64,%xs:!V)");
    text =
        replace(text, "#data.index_bound<2,3,0>", "#data.index_bound<0,1,0>");
    text = replace(text, "func.return %b,%v : !F,!F", "func.return");
    text = replace(
        text,
        "%r:2 = \"algebra.finite_fold\"(%xs,%a,%b) {domain=@items,step=@step} "
        ": (!V,!F,!F)->(!F,!F)",
        "\"algebra.finite_fold\"(%xs) {domain=@items,step=@step} : (!V)->()");
    text = replace(text, "\"protocol.return\"(%r#0,%r#1)",
                   "\"protocol.return\"(%a,%b)");
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "Unit state total fold refused");
    Operation *fold = nullptr;
    module->walk([&](algebra::FiniteFoldOp op) { fold = op; });
    finite::Summary summary;
    require(succeeded(finite::summarize(fold, summary)) &&
                summary.results.empty() &&
                llvm::any_of(summary.formation,
                             [](const auto &bits) { return bits.test(0); }),
            "Unit state erased formation obligations");
    pipeline(*module);
    refusesIR(
        replace(text, "#data.index_bound<0,1,0>", "#data.index_bound<1,0,0>"),
        context, "finite-bound");
  });
  cases.run("affine state swapping refused", [&] {
    auto module = parseSourceString<ModuleOp>(fixture("affine"), &context);
    require(bool(module), "affine fixture refused");
    auto helper = sf::function(*module, "step");
    sc::returned(helper)->setOperands(
        ValueRange{helper.getArgument(2), helper.getArgument(1)});
    std::string text;
    llvm::raw_string_ostream out(text);
    module->print(out);
    refusesIR(text, context, "execution-source-closure");
  });
  cases.run("unknown bound boolean refused", [&] {
    refusesIR(replace(fixture("total-state"),
                      "(%xs,%i) :", "(%xs,%i) {in_bounds=true} :"),
              context, "finite-bound");
  });
  cases.run("unproved index refused", [&] {
    refusesIR(replace(fixture("total-state"),
                      "data.preconditions=[#data.index_bound<2,3,0>]",
                      "data.preconditions=[]"),
              context, "finite-bound");
  });
  cases.run("wrong helper container refused", [&] {
    auto wrong = replace(fixture("total-state"), "%i:ui64,%xs:!V)",
                         "%i:ui64,%xs:!V,%ys:!V)");
    wrong = replace(wrong, "(%xs,%i) :", "(%ys,%i) :");
    wrong = replace(wrong, "(%xs,%a,%b) {domain", "(%xs,%a,%b,%xs) {domain");
    wrong = replace(wrong, "(!V,!F,!F)->(!F,!F)\n   ",
                    "(!V,!F,!F,!V)->(!F,!F)\n   ");
    refusesIR(wrong, context, "finite-bound");
  });
  cases.run("domain indices can bound a proven captured container", [&] {
    auto text = replace(fixture("total-state"), "%i:ui64,%xs:!V)",
                        "%i:ui64,%xs:!V,%ys:!V)");
    text =
        replace(text, "#data.index_bound<2,3,0>", "#data.index_bound<2,4,0>");
    text = replace(text, "(%xs,%i) :", "(%ys,%i) :");
    text = replace(text, "(%xs,%a,%b) {domain", "(%xs,%a,%b,%xs) {domain");
    text = replace(text, "(!V,!F,!F)->(!F,!F)\n   ",
                   "(!V,!F,!F,!V)->(!F,!F)\n   ");
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "exact captured-container bound refused");
    pipeline(*module);
    auto wrong = replace(text, "^entry(%xs:!V,%a:!F,%b:!F)",
                         "^entry(%xs:!V,%a:!F,%b:!F,%other:!V)");
    wrong =
        replace(wrong, "(%xs,%a,%b,%xs) {domain", "(%xs,%a,%b,%other) {domain");
    wrong = replace(wrong, "function_type=(!V,!F,!F)->(!F,!F)",
                    "function_type=(!V,!F,!F,!V)->(!F,!F)");
    wrong = replace(wrong, "input_roles=[[\"P\"],[\"P\"],[\"P\"]]",
                    "input_roles=[[\"P\"],[\"P\"],[\"P\"],[\"P\"]]");
    refusesIR(wrong, context, "finite-bound");
  });
  cases.run("dead helper polynomial observation refused", [&] {
    auto wrong = replace(
        fixture("total-state"), "   func.return",
        R"mlir(   %array = "algebra.array_from_elements"(%a,%b) : (!F,!F)-> !algebra.field_array<"bls12-381.fr", 2>
   %poly = "poly.from_coefficients"(%array) : (!algebra.field_array<"bls12-381.fr", 2>)->!poly.polynomial<"bls12-381.fr",1>
   %bad = "poly.coefficients"(%poly) : (!poly.polynomial<"bls12-381.fr",1>)->!algebra.field_array<"bls12-381.fr", 1>
   func.return)mlir");
    refusesIR(wrong, context, "polynomial-formation");
  });
  for (bool fits : {false, true})
    cases.run(fits ? "substituted polynomial observation fits"
                   : "dead substituted polynomial observation refused",
              [&] {
                std::string width = fits ? "2" : "1";
                auto text =
                    replace(fixture("total-state"), " func.func private @step",
                            " func.func private "
                            "@observe(%p:!poly.polynomial<\"bls12-381.fr\",1>)-"
                            ">!algebra.field_array<\"bls12-381.fr\", " +
                                width +
                                "> {\n"
                                "   %v = \"poly.coefficients\"(%p) : "
                                "(!poly.polynomial<\"bls12-381.fr\",1>)->!"
                                "algebra.field_array<\"bls12-381.fr\", " +
                                width +
                                ">\n"
                                "   func.return %v : "
                                "!algebra.field_array<\"bls12-381.fr\", " +
                                width + ">\n }\n func.func private @step");
                text = replace(
                    text, "   func.return %b,%v",
                    "   %array = \"algebra.array_from_elements\"(%a,%b) : "
                    "(!F,!F)-> !algebra.field_array<\"bls12-381.fr\", 2>\n"
                    "   %poly = \"poly.from_coefficients\"(%array) : "
                    "(!algebra.field_array<\"bls12-381.fr\", "
                    "2>)->!poly.polynomial<\"bls12-381.fr\",1>\n"
                    "   %dead = func.call @observe(%poly) : "
                    "(!poly.polynomial<\"bls12-381.fr\",1>)->!algebra.field_"
                    "array<\"bls12-381.fr\", " +
                        width +
                        ">\n"
                        "   func.return %b,%v");
                if (fits) {
                  auto module = parseSourceString<ModuleOp>(text, &context);
                  require(bool(module),
                          "generic polynomial helper was prematurely refused");
                  pipeline(*module);
                } else
                  refusesIR(text, context, "polynomial-formation");
              });
  cases.run("domain argument must have native encoding", [&] {
    auto text = replace(source, " \"runtime.binding\"()", R"mlir(
 "data.domain"() ({
 ^entry(%p:!poly.polynomial<"bls12-381.fr",1>,%lo:ui64,%hi:ui64):
   %d = "data.domain_range"(%lo,%hi) : (ui64,ui64)->!data.domain<ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64>)->()
 }) {sym_name="bad_domain",sym_visibility="private",function_type=(!poly.polynomial<"bls12-381.fr",1>,ui64,ui64)->!data.domain<ui64>} : ()->()
 "runtime.binding"())mlir");
    refusesIR(text, context, "finite-domain");
  });
  for (StringRef name : {"dot", "collect"})
    cases.run(name + " actual executable operand mutation", [&] {
      auto before = parseSourceString<ModuleOp>(fixture(name), &context);
      require(bool(before), "fixture refused");
      auto after = sf::prepare(*before);
      if (name == "dot") {
        auto dots = sf::executionApplications(*after, "work", "vector.dot");
        require(dots.size() == 1, "native dot missing");
        dots.front().getInputsMutable()[1].set(dots.front().getInputs()[0]);
      } else {
        require(reached(*after, "vector.mul") ||
                    reached(*after, "numerical.map"),
                "native collection missing");
        auto helper = sf::function(*after, "work");
        sc::returned(helper)->setOperand(0, helper.getArgument(1));
      }
      require(succeeded(verify(*after)), "operand mutation malformed");
      require(failed(sf::compare(*before, *after)),
              "changed native candidate accepted");
    });
  for (StringRef name : {"dot", "filter"})
    cases.run(name + " removed ignored shape guard", [&] {
      auto before = parseSourceString<ModuleOp>(fixture(name), &context);
      require(bool(before), "fixture refused");
      auto after = sf::prepare(*before);
      auto guards =
          sf::executionApplications(*after, "work", "control.require");
      require(!guards.empty(), "shape guard missing");
      sc::omit(guards.back());
      require(succeeded(verify(*after)), "guard omission malformed");
      require(failed(sf::compare(*before, *after)),
              "removed ignored guard accepted");
    });
  cases.run("actual predicate arms exchanged", [&] {
    auto before = parseSourceString<ModuleOp>(fixture("filter"), &context);
    require(bool(before), "filter fixture refused");
    auto after = sf::prepare(*before, {false, false});
    cf::CondBranchOp branch;
    after->walk([&](cf::CondBranchOp op) { branch = op; });
    require(bool(branch), "predicate branch missing");
    auto armCall = [&](Block *arm) {
      auto enter = cast<runtime::EnterScopeOp>(arm->front());
      auto dispatch = cast<exec::DispatchOp>(enter->getNextNode());
      return cast<func::CallOp>(dispatch.getReturned()->front());
    };
    auto first = armCall(branch.getTrueDest());
    auto second = armCall(branch.getFalseDest());
    auto callee = first.getCalleeAttr();
    first.setCalleeAttr(second.getCalleeAttr());
    second.setCalleeAttr(callee);
    require(succeeded(verify(*after)), "arm exchange malformed");
    require(failed(sf::compare(*before, *after)), "predicate arms exchanged");
  });
  cases.run("finite scoped static reference cycle", [&] {
    auto text = replace(source,
                        "%next = \"exec.apply\"(%scope,%state,%item) "
                        "{binding=@add,parameters=[],site=\"add\"}",
                        "%next = \"exec.fold\"(%scope,%xs,%state) "
                        "{domain=@items,step=@step,site=\"recur\"}");
    text = replace(text, "(!runtime.scope,!F,!F)->!exec.outcome<(!F)>",
                   "(!runtime.scope,!V,!F)->!exec.outcome<(!F)>");
    refusesIR(text, context, "finite-cycle");
  });
  cases.run("nested total static reference cycle", [&] {
    refusesIR(replace(fixture("nested-total"), "step=@inside", "step=@outside"),
              context, "finite-cycle");
  });
  cases.run("total helper body same symbol changed", [&] {
    auto before =
        parseSourceString<ModuleOp>(fixture("nested-total"), &context);
    auto after = parseSourceString<ModuleOp>(replace(fixture("nested-total"),
                                                     "algebra.field_add",
                                                     "algebra.field_multiply"),
                                             &context);
    require(before && after, "fixture refused");
    require(failed(mathematical::verifyProtocolPreparationPreserved(
                &before->getBody()->front(), &after->getBody()->front())),
            "changed total referenced helper accepted");
  });
  cases.run("successor sequence does not inherit bound", [&] {
    auto helper = R"mlir(
 func.func private @successor(%i:ui64,%xs:!data.sequence<i1>,%flag:i1)->i1 attributes {data.preconditions=[#data.index_bound<0,1,0>]} {
   %ys = "data.sequence_append"(%xs,%flag) : (!data.sequence<i1>,i1)->!data.sequence<i1>
   %x = "data.bounded_at"(%ys,%i) : (!data.sequence<i1>,ui64)->i1
   func.return %x : i1
 }
)mlir";
    refusesIR(replace(source, " \"runtime.binding\"()",
                      std::string(helper) + " \"runtime.binding\"()"),
              context, "finite-bound");
  });
  cases.run("shifted index does not inherit bound", [&] {
    auto text = replace(fixture("total-state"), "   %v =",
                        R"mlir(   %one = "data.index"() {value="1"} : ()->ui64
   %isSmall = "data.index_less"(%i,%one) : (ui64,ui64)->i1
   %shifted = arith.select %isSmall,%one,%i : ui64
   %v =)mlir");
    text = replace(text, "(%xs,%i) :", "(%xs,%shifted) :");
    refusesIR(text, context, "finite-bound");
  });
  cases.run("exact helper forwarding retains bound", [&] {
    auto text = replace(
        fixture("total-state"), " func.func private @step",
        R"mlir( func.func private @identity(%i:ui64)->ui64 { func.return %i : ui64 }
 func.func private @step)mlir");
    text = replace(
        text, "   %v =",
        "   %forwarded = func.call @identity(%i) : (ui64)->ui64\n   %v =");
    text = replace(text, "(%xs,%i) :", "(%xs,%forwarded) :");
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "forwarded bound refused");
    pipeline(*module);
  });
  cases.run("unknown total zip extent refused", [&] {
    auto text = replace(fixture("total-zip"), "^entry(%xs:!V,%factor:!F)",
                        "^entry(%xs:!V,%ys:!V,%factor:!F)");
    text = replace(text, "finite_collect\"(%xs,%xs,%factor)",
                   "finite_collect\"(%xs,%ys,%factor)");
    text = replace(text, "function_type=(!V,!F)->!V",
                   "function_type=(!V,!V,!F)->!V");
    text = replace(text, "input_roles=[[\"P\"],[\"P\"]]",
                   "input_roles=[[\"P\"],[\"P\"],[\"P\"]]");
    refusesIR(text, context, "finite-bound");
  });
  cases.run("forwarding evidence reuses a shared helper graph", [&] {
    std::string helpers;
    for (unsigned level = 0; level < 9; ++level) {
      helpers += " func.func private @forward_" + std::to_string(level) +
                 "(%x:ui64)->ui64 {\n";
      std::string value = "%x";
      if (level < 8)
        for (unsigned call = 0; call < 63; ++call) {
          auto next = "%v" + std::to_string(call);
          helpers += "  " + next + " = func.call @forward_" +
                     std::to_string(level + 1) + "(" + value +
                     ") : (ui64)->ui64\n";
          value = next;
        }
      helpers += "  func.return " + value + " : ui64\n }\n";
    }
    auto text = replace(fixture("total-state"), " func.func private @step",
                        helpers + " func.func private @step");
    text = replace(
        text, "   %v =",
        "   %forward = func.call @forward_0(%i) : (ui64)->ui64\n   %v =");
    text = replace(text, "(%xs,%i) :", "(%xs,%forward) :");
    // Exercise the evidence query itself. Whole-unit expanded analysis has a
    // separate operation budget and intentionally rejects this helper graph.
    ParserConfig config(&context, false);
    auto module = parseSourceString<ModuleOp>(text, config);
    require(bool(module), "forwarding graph did not parse");
    bool checked = false;
    module->walk([&](data::BoundedAtOp access) {
      require(
          finite::provesBound(access->getOperand(1), access->getOperand(0), 0),
          "shared forwarding evidence exhausted work");
      checked = true;
    });
    require(checked, "missing forwarding access");
    refusesIR(text, context, "mathematical-analysis-limit");
  });
  cases.run("fixed Sequence extent is checked through ordinary returns", [&] {
    std::string helpers = R"mlir(
 func.func private @make()->!data.sequence<i1> {
   %s = "data.sequence_empty"() : ()->!data.sequence<i1>
   %b = arith.constant true
   %t = "data.sequence_append"(%s,%b) : (!data.sequence<i1>,i1)->!data.sequence<i1>
   func.return %t : !data.sequence<i1>
 }
 func.func private @relay()->!data.sequence<i1> {
   %s = func.call @make() : ()->!data.sequence<i1>
   func.return %s : !data.sequence<i1>
 }
 func.func private @read()->i1 {
   %s = func.call @relay() : ()->!data.sequence<i1>
   %i = "data.index"() {value="0"} : ()->ui64
   %b = "data.bounded_at"(%s,%i) : (!data.sequence<i1>,ui64)->i1
   func.return %b : i1
 }
)mlir";
    auto text = replace(source, " \"runtime.binding\"()",
                        helpers + " \"runtime.binding\"()");
    require(bool(parseSourceString<ModuleOp>(text, &context)),
            "returned constructor extent refused");
    refusesIR(replace(text, "func.return %t :", "func.return %s :"), context,
              "finite-bound");
    auto unknown =
        replace(text, "@read()->i1", "@read(%unknown:!data.sequence<i1>)->i1");
    unknown = replace(unknown, "(%s,%i) :", "(%unknown,%i) :");
    refusesIR(unknown, context, "finite-bound");
  });
  cases.run("actual total multi-result candidate exchanged", [&] {
    auto before = parseSourceString<ModuleOp>(fixture("total-state"), &context);
    require(bool(before), "fixture refused");
    PassManager project(&context);
    project.addPass(protocol::createProjectProtocolPass());
    require(succeeded(project.run(*before)), "projection failed");
    OwningOpRef<ModuleOp> after(cast<ModuleOp>((*before)->clone()));
    PassManager lower(&context);
    lower.addPass(protocol::createLowerMathPass({false, false}));
    require(succeeded(lower.run(*after)), "lowering failed");
    require(succeeded(mathematical::verifyProjectionPreserved(*before, *after,
                                                              {false, false})),
            "unmodified total lowering failed independent comparison");
    // Lowering retains an actual compute request and its ordered result ports.
    // Swapping those uses in the participant must fail projection comparison.
    protocol_ir::LocalCallOp call;
    after->walk([&](protocol_ir::LocalCallOp op) {
      if (op.getNumResults() == 2)
        call = op;
    });
    require(bool(call), "multi-result calculation missing");
    SmallVector<OpOperand *> first, second;
    for (auto &use : call.getResult(0).getUses())
      first.push_back(&use);
    for (auto &use : call.getResult(1).getUses())
      second.push_back(&use);
    for (auto *use : first)
      use->set(call.getResult(1));
    for (auto *use : second)
      use->set(call.getResult(0));
    require(succeeded(verify(*after)), "result exchange malformed");
    require(failed(mathematical::verifyProjectionPreserved(*before, *after,
                                                           {false, false})),
            "exchanged total results accepted");
  });
  for (StringRef name : {"matrix-row", "matrix-column", "msm", "product"})
    cases.run(name + " native operand mutation", [&] {
      auto before = parseSourceString<ModuleOp>(fixture(name), &context);
      require(bool(before), "fixture refused");
      auto after = sf::prepare(*before);
      if (name == "msm") {
        auto equal = sf::executionApplications(*after, "work", "curve.equal");
        auto scales = sf::executionApplications(*after, "work", "curve.scale");
        require(equal.size() == 1 && scales.size() == 2,
                "missing MSM comparison or seed");
        equal.front().getInputsMutable()[0].set(
            sc::payload(scales.front()).front());
      } else {
        auto helper = sf::function(*after, "work");
        sc::returned(helper)->setOperand(
            0, helper.getArgument(helper.getNumArguments() - 1));
      }
      require(succeeded(verify(*after)), "result mutation malformed");
      require(failed(sf::compare(*before, *after)),
              "changed native result accepted");
    });
  if (checkedAccess) {
    bool installed = protocol::operationContracts("matrix.get") &&
                     protocol::operationContracts("field_array.get");
    cases.run("checked access prerequisites installed", [&] {
      require(installed, "matrix.get and field_array.get must be integrated");
    });
    if (installed) {
      for (StringRef name :
           {"fixed-elements", "matrix-row", "matrix-column", "matrix-values",
            "total-matrix-values", "bilinear"})
        for (bool optimize : {false, true})
          cases.run(name +
                        (optimize ? " optimized access" : " fallback access"),
                    [&] {
                      auto module =
                          parseSourceString<ModuleOp>(fixture(name), &context);
                      require(bool(module), "access fixture refused");
                      pipeline(*module, optimize);
                    });
      cases.run("actual bilinear operand mutation", [&] {
        auto before =
            parseSourceString<ModuleOp>(fixture("bilinear"), &context);
        require(bool(before), "bilinear source refused");
        auto after = sf::prepare(*before);
        auto products =
            sf::executionApplications(*after, "work", "matrix.bilinear");
        require(products.size() == 1, "bilinear native invocation missing");
        products.front().getInputsMutable()[2].set(
            products.front().getInputs()[1]);
        require(succeeded(verify(*after)), "bilinear mutation malformed");
        require(failed(sf::compare(*before, *after)),
                "wrong bilinear vector accepted");
      });
    }
  }
  return cases.result();
}
