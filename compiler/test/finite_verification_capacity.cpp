#include "../lib/Transforms/FiniteVerification.h"
#include "../lib/Transforms/Kernel/Schedule.h"
#include "../lib/Transforms/Kernel/Support.h"
#include "../lib/Transforms/MathematicalComparison.h"
#include "../lib/Transforms/NumericalSelection.h"
#include "../lib/Transforms/RecipeRealizations.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Contracts/RingExpression.h"
#include "zkc/Dialect/IR.h"
#include <fstream>
#include <limits>
#include <sstream>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;

namespace {
constexpr MathematicalSelectionPolicy vectorPolicy{
    true, false, false, true, NumericalExpressionMode::VectorOnly};
OwningOpRef<ModuleOp> fixture(MLIRContext &context, StringRef name) {
  std::ifstream input(std::string(ZKC_FINITE_FIXTURES) + "/" + name.str() +
                      ".mlir");
  require(bool(input), "missing fixture");
  std::ostringstream text;
  text << input.rdbuf();
  auto module = parseSourceString<ModuleOp>(text.str(), &context);
  require(bool(module) && succeeded(verify(*module)), "fixture refused");
  return module;
}
OwningOpRef<ModuleOp> clone(ModuleOp source) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(source->clone()));
}
bool same(ModuleOp left, ModuleOp right) {
  return OperationEquivalence::isEquivalentTo(
      left, right, OperationEquivalence::IgnoreLocations);
}
local::FuncOp function(ModuleOp module, StringRef name) {
  return SymbolTable(&module.getBody()->front()).lookup<local::FuncOp>(name);
}
Operation *payload(local::FuncOp target, SymbolTable &symbols) {
  for (auto &op : target.getBody().front())
    if (mathematical::hasFinitePayloadContract(&op, symbols))
      return &op;
  return nullptr;
}
bool hasLoop(ModuleOp module, StringRef name) {
  bool result = false;
  function(module, name).walk([&](local::LocalForOp) { result = true; });
  return result;
}
OwningOpRef<ModuleOp> kernelReductions(MLIRContext &context) {
  auto result = parseSourceString<ModuleOp>(R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { module @reductions attributes {exec.computation} {
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 func.func private @add(%acc:!F,%x:!F,%xs:!V)->!F {
   %s = "algebra.field_add"(%acc,%x) : (!F,!F)->!F
   func.return %s : !F
 }
 func.func private @multiply(%acc:!F,%x:!F,%xs:!V)->!F {
   %s = "algebra.field_multiply"(%acc,%x) : (!F,!F)->!F
   func.return %s : !F
 }
 func.func @evaluate(%xs:!V,%zero:!F,%one:!F)->(!F,!F) {
   %sum = "algebra.finite_fold"(%xs,%zero) {domain=@items,step=@add} : (!V,!F)->!F
   %product = "algebra.finite_fold"(%xs,%one) {domain=@items,step=@multiply} : (!V,!F)->!F
   func.return %sum,%product : !F,!F
 }
} }
)mlir",
                                            &context);
  require(bool(result) && succeeded(verify(*result)),
          "two-occurrence Kernel fixture did not admit");
  return result;
}
OwningOpRef<ModuleOp> nestedKernelReductions(MLIRContext &context) {
  auto result = parseSourceString<ModuleOp>(R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { module @reductions attributes {exec.computation} {
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 func.func private @add(%acc:!F,%x:!F,%xs:!V)->!F {
   %s = "algebra.field_add"(%acc,%x) : (!F,!F)->!F
   func.return %s : !F
 }
 func.func private @nested(%acc:!F,%x:!F,%xs:!V)->!F {
   %first = "algebra.finite_fold"(%xs,%acc) {domain=@items,step=@add} : (!V,!F)->!F
   %second = "algebra.finite_fold"(%xs,%first) {domain=@items,step=@add} : (!V,!F)->!F
   %s = "algebra.field_add"(%second,%x) : (!F,!F)->!F
   func.return %s : !F
 }
 func.func @evaluate(%xs:!V,%zero:!F)->!F {
   %sum = "algebra.finite_fold"(%xs,%zero) {domain=@items,step=@nested} : (!V,!F)->!F
   func.return %sum : !F
 }
} }
)mlir",
                                            &context);
  require(bool(result) && succeeded(verify(*result)),
          "nested Kernel fixture did not admit");
  return result;
}
void requiredReaderCapacity(const finite::VerificationResult &outcome) {
  require(outcome.status == finite::VerificationStatus::RequiredCapacity &&
              outcome.detail == "finite reader work" && outcome.capacity &&
              outcome.capacity->owner == WorkOwner::RequiredFiniteReader &&
              outcome.capacity->available == 0,
          "nested reader lost its typed required capacity cause");
}
// Extend the ordinary square into x^(multiplications + 1). Both scalar and
// vector operations stay well formed, and the two actual formulas agree.
void extendProduct(local::FuncOp target, unsigned multiplications) {
  auto &block = target.getBody().front();
  auto *prototype = block.back().getOperand(0).getDefiningOp();
  require(prototype && prototype->getNumOperands() == 2,
          "missing multiplication prototype");
  OpBuilder builder(&block.back());
  Value result = prototype->getResult(0);
  for (unsigned i = 1; i < multiplications; ++i) {
    auto *next = builder.clone(*prototype);
    next->setOperands({result, target.getArgument(0)});
    next->setAttr("site",
                  builder.getStringAttr("product_" + std::to_string(i)));
    result = next->getResult(0);
  }
  block.back().setOperand(0, result);
}
// Probe the actual comparator independently of the producer's operation order.
FailureOr<Value> compare(ModuleOp source, ModuleOp candidate, StringRef name,
                         uint64_t &work,
                         mathematical::ComparisonCapacity &capacity) {
  SymbolTable before(&source.getBody()->front());
  finite::Computation computation;
  require(succeeded(finite::describe(before.lookup(name), computation)),
          "finite description failed");
  SymbolTable symbols(&candidate.getBody()->front());
  auto target = function(candidate, name);
  Operation *cursor = payload(target, symbols);
  require(cursor, "candidate has no bulk payload");
  auto *saved = cursor;
  llvm::DenseSet<Operation *> bindings;
  auto result = mathematical::compareFinitePayload(
      computation, target.getArguments(),
      target.getBody().front().front().getResult(0), cursor, symbols, bindings,
      work, &target.getBody().front().back(), &capacity);
  if (failed(result))
    require(cursor == saved && bindings.empty(),
            "failed comparison published cursor or bindings");
  else
    require(cursor == &target.getBody().front().back() &&
                *result == cursor->getOperand(0),
            "comparison did not verify the actual returned value");
  return result;
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  for (bool scheduled : {false, true})
    cases.run(
        scheduled ? "nested scheduled readers share actual work"
                  : "nested Local readers share actual work",
        [&] {
          auto source = nestedKernelReductions(context);
          auto original = clone(*source);
          auto unit = *source->getBody()->getOps<mlir::ModuleOp>().begin();
          mathematical::RealizationWork work;
          work.requiredFiniteChecking = 1000;
          work.optionalFiniteChecking = 0;
          uint64_t copies = 1000000, bytes = 16 * 1024 * 1024;
          auto ordered = kernel::realizeEntry(unit, "nested", {false, false},
                                              work, copies, bytes);
          require(bool(ordered), "outer reader starved its nested callbacks");
          unsigned loops = 0, nestedLoops = 0;
          ordered->walk([&](local::LocalForOp loop) {
            ++loops;
            nestedLoops += bool(loop->getParentOfType<local::LocalForOp>());
          });
          require(loops == 3 && nestedLoops == 2,
                  "fixture lost its outer fold or sibling nested folds");
          auto candidate = scheduled ? kernel::scheduleEntry(*ordered, copies)
                                     : clone(*ordered);
          require(bool(candidate), "nested schedule construction refused");
          auto before = clone(*candidate);
          finite::VerificationResult outcome{
              finite::VerificationStatus::Mismatch, {}};
          auto check = [&](uint64_t localCap, uint64_t &shared) {
            finite::VerificationLimits limits{localCap, 0, &shared};
            return scheduled
                       ? kernel::verifyEntrySchedule(unit, *candidate, "nested",
                                                     {false, false}, limits,
                                                     &outcome)
                       : kernel::verifyEntryRecipes(unit, *candidate, "nested",
                                                    {false, false}, limits,
                                                    &outcome);
          };
          uint64_t shared = 1000;
          require(succeeded(check(100000, shared)) &&
                      outcome.status == finite::VerificationStatus::Verified,
                  "ample shared nested check refused");
          const uint64_t cost = 1000 - shared;
          require(cost > 1 && cost < 1000,
                  "nested check did not debit actual shared work");
          uint64_t localCap = 0;
          for (; localCap <= cost; ++localCap) {
            shared = 1000;
            if (succeeded(check(localCap, shared)))
              break;
            requiredReaderCapacity(outcome);
          }
          require(
              localCap > 1 && localCap < cost,
              "nested work was charged to one reader instead of local caps");
          shared = cost;
          require(succeeded(check(localCap, shared)) && shared == 0,
                  "exact cumulative nested allowance refused");
          shared = cost - 1;
          require(failed(check(localCap, shared)) && shared == 0,
                  "one-short cumulative nested allowance was replenished");
          requiredReaderCapacity(outcome);
          if (!scheduled)
            require(outcome.capacity->requested == 1,
                    "failed instruction lost its requested debit");
          shared = 1000;
          require(failed(check(localCap - 1, shared)) && shared > 0,
                  "shared work bypassed the per-reader local cap");
          requiredReaderCapacity(outcome);
          shared = 2 * cost;
          require(
              succeeded(check(localCap, shared)) && shared == cost &&
                  succeeded(check(localCap, shared)) && shared == 0 &&
                  failed(check(localCap, shared)) && shared == 0,
              "nested checks refunded work or reset the containing balance");
          requiredReaderCapacity(outcome);
          const auto maximum = std::numeric_limits<uint64_t>::max();
          shared = maximum;
          require(succeeded(check(maximum, shared)) && shared == maximum - cost,
                  "nested accounting overflowed at the maximum allowance");
          require(failed(check(0, shared)) && shared == maximum - cost,
                  "zero local cap spent or replenished shared work");
          requiredReaderCapacity(outcome);
          shared = 0;
          require(failed(check(maximum, shared)) && shared == 0,
                  "zero shared work underflowed");
          requiredReaderCapacity(outcome);
          require(same(*source, *original) && same(*candidate, *before) &&
                      work.optionalFiniteChecking == 0,
                  "nested checking edited IR or spent optional work");
        });
  cases.run("nested construction exact and one-short checks are atomic", [&] {
    auto source = nestedKernelReductions(context);
    auto original = clone(*source);
    auto unit = *source->getBody()->getOps<mlir::ModuleOp>().begin();
    mathematical::RealizationWork work;
    work.requiredFiniteChecking = 1000;
    work.optionalFiniteChecking = 0;
    uint64_t copies = 1000000, bytes = 16 * 1024 * 1024;
    auto measured = kernel::realizeEntry(unit, "nested", {false, false}, work,
                                         copies, bytes);
    require(bool(measured), "nested construction measurement refused");
    const uint64_t cost = 1000 - work.requiredFiniteChecking;
    require(cost > 1 && cost < 1000,
            "nested construction did not share required checking work");
    work = {};
    work.requiredFiniteChecking = cost;
    work.optionalFiniteChecking = 0;
    copies = 1000000;
    bytes = 16 * 1024 * 1024;
    auto exact = kernel::realizeEntry(unit, "nested", {false, false}, work,
                                      copies, bytes);
    require(bool(exact) && work.requiredFiniteChecking == 0 &&
                same(*measured, *exact),
            "exact nested construction allowance changed or refused output");
    work = {};
    work.requiredFiniteChecking = cost - 1;
    work.optionalFiniteChecking = 0;
    copies = 1000000;
    bytes = 16 * 1024 * 1024;
    mathematical::VerificationDecision outcome;
    auto refused =
        kernel::realizeEntry(unit, "nested", {false, false}, work, copies,
                             bytes, {}, nullptr, nullptr, &outcome);
    require(!refused && work.requiredFiniteChecking == 0 &&
                outcome.outcome ==
                    mathematical::VerificationObservation::RequiredCapacity &&
                outcome.detail == "finite reader work" && outcome.capacity &&
                outcome.capacity->owner == WorkOwner::RequiredFiniteReader &&
                outcome.capacity->available == 0 && same(*source, *original) &&
                same(*measured, *exact),
            "one-short nested construction published output or lost capacity");
  });
  cases.run("Kernel optional retries debit both occurrences cumulatively", [&] {
    auto source = kernelReductions(context);
    auto before = clone(*source);
    auto unit = *source->getBody()->getOps<mlir::ModuleOp>().begin();
    mathematical::NumericalSelection session;
    auto initial = session.work;
    auto candidate = kernel::realizeEntry(
        unit, "reductions", {}, session.work, session.remainingCopy,
        session.remainingSiteBytes, {100000, 1}, nullptr, &session);
    require(bool(candidate),
            "attributable optional retries refused ordered source");
    unsigned loops = 0;
    candidate->walk([&](local::LocalForOp) { ++loops; });
    require(
        loops == 2 && same(*source, *before) &&
            succeeded(
                kernel::verifyEntryRecipes(unit, *candidate, "reductions")),
        "targeted retries changed source or lost independent correspondence");
    require(session.work.discardedRecipeCopy < initial.discardedRecipeCopy &&
                session.work.matching.structural <
                    initial.matching.structural &&
                session.work.helperOperations < initial.helperOperations &&
                session.work.finiteExpressions < initial.finiteExpressions,
            "discarded attempts replenished cumulative construction or "
            "discovery work");
  });
  cases.run(
      "Kernel ordered copy exact and one-short boundaries are atomic", [&] {
        auto source = kernelReductions(context);
        auto before = clone(*source);
        auto unit = *source->getBody()->getOps<mlir::ModuleOp>().begin();
        mathematical::RealizationWork work;
        uint64_t copies = 1000000, bytes = 16 * 1024 * 1024;
        auto measured = kernel::realizeEntry(unit, "boundary", {false, false},
                                             work, copies, bytes);
        require(bool(measured), "ordered copy measurement refused");
        uint64_t cost = 1000000 - copies;
        require(cost > 1, "ordered construction did not charge copies");
        work = {};
        copies = cost;
        bytes = 16 * 1024 * 1024;
        require(bool(kernel::realizeEntry(unit, "boundary", {false, false},
                                          work, copies, bytes)) &&
                    copies == 0,
                "exact ordered copy allowance refused");
        work = {};
        copies = cost - 1;
        bytes = 16 * 1024 * 1024;
        ScopedDiagnosticHandler quiet(&context,
                                      [](Diagnostic &) { return success(); });
        require(
            !kernel::realizeEntry(unit, "boundary", {false, false}, work,
                                  copies, bytes) &&
                same(*source, *before),
            "one-short required copy capacity published a partial candidate");
      });
  cases.run("owned occurrence discovery and catalog visits share one ceiling",
            [&] {
              mathematical::RealizationSubject first;
              first.declaration = "evaluate";
              first.position = {0, 0, 0};
              auto second = first;
              second.position.back() = 1;
              mathematical::NumericalSelection session;
              session.work.selectionBookkeeping = 1;
              auto id = session.discover(first, true);
              require(bool(id) && session.work.selectionBookkeeping == 0,
                      "exact discovery allowance refused");
              auto unavailable = session.discover(second, true);
              require(!unavailable && !session.chargeCatalog(),
                      "another occurrence or catalog visit replenished "
                      "discovery allowance");
              auto reason = llvm::toString(unavailable.takeError());
              require(namesIdentifier(reason, "finite-analysis-limit"),
                      "discovery capacity lost its identifier");
            });
  for (StringRef name : {"collect", "dot", "matrix-row", "matrix-column",
                         "bilinear", "msm-direct"}) {
    StringRef declaration = name == "collect" ? "collect" : "fold";
    cases.run(name + " precise independent comparison boundary", [&] {
      auto source = fixture(context, name);
      auto candidate = clone(*source);
      require(succeeded(finite::realizeLocals(*candidate, vectorPolicy)),
              "bulk realization failed");
      auto target = function(*candidate, declaration);
      auto *result =
          target.getBody().front().back().getOperand(0).getDefiningOp();
      require(result && result->getNumOperands() == 2,
              "fixture no longer returns a binary bulk result");
      Value left = result->getOperand(0), right = result->getOperand(1);
      result->setOperands({right, left});
      require(succeeded(verify(*candidate)) &&
                  succeeded(finite::verifyRealizations(*source, *candidate)),
              "commuted valid candidate was refused");
      uint64_t work = 100000;
      mathematical::ComparisonCapacity capacity;
      require(succeeded(
                  compare(*source, *candidate, declaration, work, capacity)) &&
                  capacity == mathematical::ComparisonCapacity::None,
              "ample comparison refused");
      uint64_t cost = 100000 - work;
      require(cost > 1, "missing comparator charges");
      work = cost;
      require(succeeded(
                  compare(*source, *candidate, declaration, work, capacity)) &&
                  work == 0 &&
                  capacity == mathematical::ComparisonCapacity::None,
              "successful exact allowance was classified as capacity");
      work = cost - 1;
      require(
          failed(compare(*source, *candidate, declaration, work, capacity)) &&
              capacity == mathematical::ComparisonCapacity::Work && work == 0,
          "failed final charge did not report work capacity");
      auto checked =
          finite::checkRealizations(*source, *candidate, {100000, 1});
      require(checked.status == finite::VerificationStatus::OptionalCapacity &&
                  checked.detail == "finite comparison work",
              "optional capacity was reported as semantic mismatch");
      llvm::outs() << name << " comparison work: " << cost << '\n';
    });
    cases.run(name + " changed result remains a hard refusal", [&] {
      auto source = fixture(context, name);
      auto candidate = clone(*source);
      require(succeeded(finite::realizeLocals(*candidate, vectorPolicy)),
              "bulk realization failed");
      auto target = function(*candidate, declaration);
      target.getBody().front().back().setOperand(
          0, name == "collect" ? target.getArgument(0)
                               : target.getArguments().back());
      require(succeeded(verify(*candidate)),
              "changed result was not an ordinary well-formed candidate");
      auto checked = finite::checkRealizations(*source, *candidate);
      require(checked.status == finite::VerificationStatus::Mismatch,
              "changed result was downgraded to capacity");
      std::string diagnostic;
      ScopedDiagnosticHandler capture(&context, [&](Diagnostic &d) {
        diagnostic += d.str();
        return success();
      });
      require(failed(checked.diagnose(*candidate)) &&
                  namesIdentifier(diagnostic, "finite-correspondence"),
              "mismatch lost its refusal identifier");
    });
    cases.run(name + " optional capacity retries checked ordered source", [&] {
      auto source = fixture(context, name);
      auto fallback = clone(*source), ordered = clone(*source);
      mathematical::RealizationWork work;
      const auto initial = work;
      std::string diagnostic;
      ScopedDiagnosticHandler capture(&context, [&](Diagnostic &d) {
        diagnostic += d.str();
        return success();
      });
      require(succeeded(finite::realizeLocalsWithLimits(
                  *fallback, vectorPolicy, &work,
                  mathematical::mathematicalRecipes(), {100000, 1})) &&
                  diagnostic.empty(),
              "transient capacity did not retry silently");
      require(
          succeeded(finite::realizeLocals(*ordered, {false, false})) &&
              hasLoop(*fallback, declaration) && same(*fallback, *ordered) &&
              succeeded(finite::verifyRealizations(*source, *fallback)),
          "fallback differs from independently checked ordered realization");
      if (name == "collect")
        require(work.lanes < initial.lanes,
                "discarded candidate replenished optional lane work");
      require(work.matching.structural < initial.matching.structural,
              "discarded candidate replenished optional matching work");
    });
    cases.run(name + " required reader boundary and atomic refusal", [&] {
      auto source = fixture(context, name);
      auto original = clone(*source), ordered = clone(*source);
      require(succeeded(finite::realizeLocals(*ordered, {false, false})),
              "ordered realization failed");
      uint64_t cost = 0;
      for (; cost < 1000; ++cost) {
        auto checked = finite::checkRealizations(*source, *ordered, {cost, 0});
        if (checked.status == finite::VerificationStatus::Verified)
          break;
        require(checked.status ==
                        finite::VerificationStatus::RequiredCapacity &&
                    checked.detail == "finite reader work",
                "required reader exhaustion became a mismatch");
      }
      require(cost > 1 && cost < 1000, "missing ordered reader boundary");
      std::string diagnostic;
      ScopedDiagnosticHandler capture(&context, [&](Diagnostic &d) {
        diagnostic += d.str();
        return success();
      });
      require(failed(finite::realizeLocalsWithLimits(
                  *source, vectorPolicy, nullptr,
                  mathematical::mathematicalRecipes(), {cost - 1, 1})) &&
                  same(*source, *original) &&
                  namesIdentifier(diagnostic, "finite-verification-capacity") &&
                  diagnostic.find("finite reader work") != std::string::npos,
              "required refusal published a partial source or lost its budget");
      llvm::outs() << name << " ordered reader work: " << cost << '\n';
    });
  }
  cases.run("ordinary valid formula reaches independent term depth limit", [&] {
    auto source = fixture(context, "collect");
    auto candidate = clone(*source);
    require(succeeded(finite::realizeLocals(*candidate, vectorPolicy)),
            "initial collect realization failed");
    extendProduct(function(*source, "square"), ring::Limits::depth);
    extendProduct(function(*candidate, "square"), ring::Limits::depth);
    extendProduct(function(*candidate, "collect"), ring::Limits::depth);
    require(succeeded(verify(*source)) && succeeded(verify(*candidate)),
            "deep equivalent formulas were not admitted");
    uint64_t work = 100000;
    mathematical::ComparisonCapacity capacity;
    require(failed(compare(*source, *candidate, "collect", work, capacity)) &&
                work > 0 && capacity == mathematical::ComparisonCapacity::Depth,
            "term depth failure was conflated with work or mismatch");
    auto checked = finite::checkRealizations(*source, *candidate);
    require(checked.status == finite::VerificationStatus::OptionalCapacity &&
                checked.detail == "finite comparison term depth",
            "depth exhaustion did not reach the transaction boundary");
    auto ordered = clone(*source);
    require(
        succeeded(finite::realizeLocals(*ordered, {false, false})) &&
            succeeded(finite::verifyRealizations(*source, *ordered)),
        "admitted deep formula lost its independently checked ordered path");
  });
  return cases.result();
}
