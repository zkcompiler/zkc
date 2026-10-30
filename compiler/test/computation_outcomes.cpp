#include "../lib/Transforms/ComputationSelection.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/ComputationFixture.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include <fstream>
#include <sstream>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
using namespace zkc::mathematical;
namespace {
std::string fixture(StringRef name) {
  std::ifstream input(std::string(ZKC_FINITE_FIXTURES) + "/" + name.str() +
                      ".mlir");
  require(bool(input), "missing fixture");
  std::ostringstream out;
  out << input.rdbuf();
  return out.str();
}
const char *capturedReduction = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_indices"(%xs) {axis=0:i64} : (!V)->!data.domain<ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<ui64>} : ()->()
 func.func private @step(%s:!F,%i:ui64,%xs:!V,%ys:!V)->!F attributes {data.preconditions=[#data.index_bound<1,3,0>]} {
   %x = "data.bounded_at"(%ys,%i) : (!V,ui64)->!F
   %r = algebra.field_add %s,%x : (!F,!F)->!F
   func.return %r : !F
 }
 "protocol.func"() ({ ^entry(%xs:!V,%seed:!F):
   %r = "algebra.finite_fold"(%xs,%seed,%xs) {domain=@items,step=@step} : (!V,!F,!V)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run("exact-zero unsupported differs from a failed debit", [&] {
    auto source =
        parseSourceString<ModuleOp>(fixture("total-predicate"), &context);
    require(bool(source) && succeeded(zkc::admitStage(*source)),
            "fixture refused");
    auto c = readComputation(*source);
    finite::ComputationWork measured;
    auto initial = measured.equations;
    auto unsupported = selectComputation(c, {}, measured);
    auto cost = initial - measured.equations;
    require(cost && unsupported.outcome() == OptimizationStatus::Unsupported,
            "control unexpectedly recognized");
    finite::ComputationWork exact;
    exact.equations = cost;
    auto result = selectComputation(c, {}, exact);
    require(!exact.equations &&
                result.outcome() == OptimizationStatus::Unsupported &&
                !result.diagnostic.outcome.capacity,
            "zero balance was reported as exhaustion");
    finite::ComputationWork shortWork;
    shortWork.equations = cost - 1;
    result = selectComputation(c, {}, shortWork);
    require(result.outcome() == OptimizationStatus::Capacity &&
                result.diagnostic.outcome.capacity &&
                result.diagnostic.outcome.capacity->owner ==
                    WorkOwner::Equations &&
                result.diagnostic.outcome.capacity->requested &&
                result.diagnostic.outcome.capacity->available &&
                *result.diagnostic.outcome.capacity->requested >
                    *result.diagnostic.outcome.capacity->available,
            "failed equation debit lost its exact cause");
  });
  cases.run("actual matching exhaustion clears tentative matches", [&] {
    auto source = parseSourceString<ModuleOp>(fixture("dot"), &context);
    require(bool(source), "fixture refused");
    auto computation = readComputation(*source);
    auto view = finite::analyzeComputation(computation);
    require(bool(view), "view missing");
    finite::ComputationWork measured;
    uint64_t initial = measured.equations;
    require(bool(matchComputation(*view, measured).reduction),
            "control failed to match");
    uint64_t cost = initial - measured.equations;
    finite::ComputationWork exact;
    exact.equations = cost;
    finite::ComputationDiagnostic diagnostic;
    require(bool(matchComputation(*view, exact, &diagnostic).reduction) &&
                !exact.equations &&
                diagnostic.outcome.status == OptimizationStatus::Succeeded,
            "exact cost success was lost");
    exact.equations = cost - 1;
    auto declined = matchComputation(*view, exact, &diagnostic);
    require(!declined.reduction && !declined.bilinear &&
                !declined.elementwise &&
                diagnostic.outcome.status == OptimizationStatus::Capacity,
            "tentative matches survived an actual failed debit");
  });
  cases.run("nested exact-zero unsupported and exhaustion", [&] {
    auto source = parseSourceString<ModuleOp>(fixture("sum"), &context);
    require(bool(source), "fixture refused");
    auto computation = readComputation(*source);
    auto view = finite::analyzeComputation(computation);
    require(bool(view), "view missing");
    finite::ComputationWork work;
    work.equations = 1;
    auto result = selectNestedContraction(*view, work);
    require(!work.equations &&
                result.outcome() == OptimizationStatus::Unsupported,
            "nested terminal zero became capacity");
    result = selectNestedContraction(*view, work);
    require(result.outcome() == OptimizationStatus::Capacity &&
                result.diagnostic.outcome.capacity->requested == 1 &&
                result.diagnostic.outcome.capacity->available == 0,
            "nested actual debit was lost");
  });
  cases.run(
      "missing evidence remains a successful partial structural view", [&] {
        auto source = parseSourceString<ModuleOp>(capturedReduction, &context);
        require(bool(source) && succeeded(zkc::admitStage(*source)),
                "control refused");
        auto c = readComputation(*source);
        finite::ComputationWork work;
        finite::ComputationDiagnostic diagnostic;
        auto view = finite::analyzeComputation(c, work, &diagnostic);
        require(
            view && view->accesses.empty() &&
                view->accessDeclines.size() == 1 &&
                diagnostic.outcome.status == OptimizationStatus::Succeeded &&
                view->accessDeclines[0].outcome.status ==
                    OptimizationStatus::MissingEvidence &&
                view->accessDeclines[0].outcome.reason ==
                    OptimizationReason::EqualExtent,
            "unknown access evidence discarded the view or became unsupported");
        auto selection = selectComputation(c, {});
        require(selection.outcome() == OptimizationStatus::MissingEvidence &&
                    selection.diagnostic.subject ==
                        view->accessDeclines[0].subject,
                "equation lost the actual missing access query");
        work = {};
        work.evidence = 0;
        selection = selectComputation(c, {}, work);
        require(selection.view && selection.view->accesses.empty() &&
                    selection.outcome() == OptimizationStatus::Capacity &&
                    selection.diagnostic.outcome.reason ==
                        OptimizationReason::EqualExtent &&
                    selection.diagnostic.outcome.capacity->owner ==
                        WorkOwner::Evidence &&
                    selection.diagnostic.outcome.capacity->available == 0 &&
                    selection.diagnostic.outcome.capacity->requested,
                "evidence capacity was erased or invented from a balance");
      });
  cases.run(
      "an unrelated failed extent probe does not poison a supported equation",
      [&] {
        auto source =
            parseSourceString<ModuleOp>(fixture("indexed-zip-dot"), &context);
        require(bool(source) && succeeded(zkc::admitStage(*source)),
                "indexed control refused");
        auto c = readComputation(*source);
        finite::ComputationWork work;
        work.evidence = 0;
        auto selection = selectComputation(c, {}, work);
        require(selection.view && selection.view->accesses.size() == 2 &&
                    selection.kind == RealizationKind::Reduction &&
                    selection.outcome() == OptimizationStatus::Succeeded &&
                    selection.diagnostic.outcome.status ==
                        OptimizationStatus::Succeeded,
                "a failed probe overrode another sufficient source-domain "
                "identity");
      });
  cases.run(
      "structural exhaustion records the actual requested allowance", [&] {
        auto source = parseSourceString<ModuleOp>(fixture("dot"), &context);
        require(bool(source), "fixture refused");
        finite::ComputationWork work;
        work.structural = 0;
        auto result = selectComputation(readComputation(*source), {}, work);
        require(!result.view &&
                    result.outcome() == OptimizationStatus::Capacity &&
                    result.diagnostic.outcome.capacity->owner ==
                        WorkOwner::Structural &&
                    result.diagnostic.outcome.capacity->available == 0 &&
                    *result.diagnostic.outcome.capacity->requested > 0,
                "structural debit was not recorded at failure");
      });
  cases.run(
      "disabled restricted and absent recipes retain distinct outcomes", [&] {
        auto source = parseSourceString<ModuleOp>(fixture("sum"), &context);
        require(bool(source), "fixture refused");
        auto c = readComputation(*source);
        MathematicalRecipes absent{{}, {}, {}};
        require(selectComputation(c, {}, absent).outcome() ==
                    OptimizationStatus::MissingRecipe,
                "missing recipe was hidden");
        auto disabled = selectComputation(c, {false, false});
        require(disabled.outcome() == OptimizationStatus::PolicyDisabled &&
                    disabled.equations.reduction,
                "policy disablement erased recognition");
        auto &op = c.helper->getRegion(0).front().front();
        auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
            &op, op.getAttrOfType<FlatSymbolRefAttr>("binding"));
        require(bool(binding), "missing binding");
        binding.setImplementation("arkworks/field.add");
        require(succeeded(zkc::admitStage(*source)), "supported pin refused");
        c = readComputation(*source);
        auto restricted = selectComputation(c, {});
        require(restricted.equations.reduction &&
                    restricted.outcome() ==
                        OptimizationStatus::ReplacementRestricted,
                "replacement restriction became a recognition failure");
      });
  cases.run("capacity and equation diagnostics retain nested occurrences", [&] {
    auto source =
        parseSourceString<ModuleOp>(fixture("nested-total"), &context);
    require(bool(source), "fixture refused");
    auto c = readComputation(*source);
    auto &body = c.helper->getRegion(0).front();
    OpBuilder builder(&body.back());
    builder.clone(body.front());
    require(succeeded(zkc::admitStage(*source)),
            "repeated helper fixture refused");
    finite::ComputationWork measured;
    auto initial = measured.structural;
    auto view = finite::analyzeComputation(c, measured);
    require(view && view->nested.size() == 2, "missing repeated occurrences");
    bool first = false, second = false;
    for (uint64_t budget = 0; budget < initial - measured.structural;
         ++budget) {
      finite::ComputationWork work;
      work.structural = budget;
      finite::ComputationDiagnostic diagnostic;
      require(!finite::analyzeComputation(c, work, &diagnostic),
              "insufficient structural work was admitted");
      require(diagnostic.outcome.status == OptimizationStatus::Capacity &&
                  !diagnostic.occurrencePath.empty() &&
                  diagnostic.occurrencePath.front() == c.operation,
              "failed debit lost its enclosing occurrence");
      first |= diagnostic.occurrencePath == view->nested[0].occurrencePath;
      second |= diagnostic.occurrencePath == view->nested[1].occurrencePath;
    }
    require(first && second, "repeated helper failures were not distinguished");
    for (const auto &child : view->nested) {
      finite::ComputationWork work;
      work.equations = 0;
      finite::ComputationDiagnostic diagnostic;
      matchComputation(child, work, &diagnostic);
      require(diagnostic.outcome.status == OptimizationStatus::Capacity &&
                  diagnostic.occurrencePath == child.occurrencePath,
              "equation failure lost its nested occurrence");
    }
  });
  return cases.result();
}
