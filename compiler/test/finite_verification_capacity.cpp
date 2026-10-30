#include "../lib/Transforms/Computation/Schedule.h"
#include "../lib/Transforms/Computation/Support.h"
#include "../lib/Transforms/FiniteVerification.h"
#include "../lib/Transforms/MathematicalComparison.h"
#include "../lib/Transforms/NumericalSelection.h"
#include "../lib/Transforms/ScopedCandidate.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ScopedComputation.h"
#include "support/ScopedFinite.h"
#include "zkc/Contracts/RingExpression.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/IR.h"
#include <fstream>
#include <limits>
#include <sstream>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;

namespace {
namespace sf = scopedFinite;
namespace sc = scopedComputation;
using Observation = mathematical::VerificationObservation;
constexpr MathematicalSelectionPolicy vectorPolicy{
    true, false, false, true, NumericalExpressionMode::VectorOnly};
OwningOpRef<ModuleOp> fixture(MLIRContext &context, StringRef name) {
  std::ifstream input(std::string(ZKC_FINITE_FIXTURES) + "/" + name.str() +
                      ".mlir");
  require(bool(input), "missing fixture");
  std::ostringstream text;
  text << input.rdbuf();
  auto module = parseSourceString<ModuleOp>(text.str(), &context);
  require(bool(module) && succeeded(zkc::admitStage(*module)),
          "fixture refused");
  // Exercise the finite expression itself as a scoped entry. The complete
  // protocol fixtures also test their surrounding arithmetic elsewhere; this
  // fixture exposes every finite input (including the MSM seed) as a port.
  Operation *original = nullptr;
  module->walk([&](Operation *op) {
    if (finite::isComputation(op))
      original = op;
  });
  finite::Computation computation;
  require(original && succeeded(finite::describe(original, computation)),
          "fixture has no finite expression");
  auto operationName = original->getName().getStringRef();
  auto attributes = original->getAttrDictionary();
  auto outcome = original->getResult(0).getType();
  auto target = sf::function(*module, "work");
  SmallVector<Type> arguments{runtime::ScopeType::get(&context)};
  llvm::append_range(arguments, computation.signature.getInputs());
  target.getBody().dropAllReferences();
  target.getBody().getBlocks().clear();
  target.setType(FunctionType::get(&context, arguments, outcome));
  auto *entry = target.addEntryBlock();
  OpBuilder builder(entry, entry->end());
  exec::ScopedExecutionBuilder control(builder, target);
  auto values =
      control.invoke(operationName, computation.signature.getResults(),
                     target.getArguments(), attributes.getValue());
  control.returned(values);
  auto owner = cast<protocol_ir::ProtocolModuleOp>(module->getBody()->front());
  for (auto function : llvm::make_early_inc_range(
           owner.getBody().front().getOps<protocol_ir::MathematicalOp>()))
    function.erase();
  require(succeeded(zkc::admitStage(*module)),
          "isolated finite source refused");
  return module;
}
OwningOpRef<ModuleOp> clone(ModuleOp source) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(source->clone()));
}
bool same(ModuleOp left, ModuleOp right) {
  return OperationEquivalence::isEquivalentTo(
      left, right, OperationEquivalence::IgnoreLocations);
}
// Count execution occurrences through outlined bodies, rather than lexical
// nesting of functions. The same called body contributes once per invocation.
std::pair<unsigned, unsigned> loopCounts(ModuleOp module, StringRef root) {
  auto closure =
      take(protocol::readSourceExecutionClosure(&module.getBody()->front()));
  unsigned loops = 0, nested = 0;
  std::function<void(StringRef, unsigned, unsigned)> visit =
      [&](StringRef name, unsigned depth, unsigned rangeDepth) {
        require(depth < 64, "test callback depth exceeded");
        for (const auto &step : closure.bodies.at(name.str())) {
          bool range = isa<exec::RangeOp>(step.operation);
          if (range) {
            ++loops;
            nested += rangeDepth != 0;
          }
          for (auto region : step.regions)
            visit(region.getSymName(), depth + 1, rangeDepth + range);
          if (auto call = dyn_cast<func::CallOp>(step.operation))
            if (closure.bodies.count(call.getCallee().str()))
              visit(call.getCallee(), depth + 1, rangeDepth);
        }
      };
  visit(root, 0, 0);
  return {loops, nested};
}
OwningOpRef<ModuleOp>
prepare(ModuleOp source, mathematical::RealizationWork &work,
        MathematicalSelectionPolicy policy = vectorPolicy,
        mathematical::VerificationDecision *outcome = nullptr) {
  uint64_t copy = 1000000, bytes = 16 * 1024 * 1024;
  std::optional<CapacityCause> capacity;
  return protocol::prepareScopedFinite(source, work, copy, bytes, capacity,
                                       policy, nullptr, nullptr, outcome);
}
mathematical::VerificationDecision check(ModuleOp source, ModuleOp candidate,
                                         uint64_t reader = 1000000,
                                         uint64_t comparison = 1000000) {
  mathematical::RealizationWork work;
  work.requiredFiniteChecking = reader;
  work.optionalFiniteChecking = comparison;
  mathematical::VerificationDecision outcome;
  ScopedDiagnosticHandler quiet(source.getContext(),
                                [](Diagnostic &) { return success(); });
  auto checked = protocol::verifyScopedFinitePreparation(source, candidate,
                                                         work, {}, &outcome);
  require(succeeded(checked) == (outcome.outcome == Observation::Verified),
          "scoped comparison lost its typed outcome");
  return outcome;
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
  require(bool(result) && succeeded(zkc::admitStage(*result)),
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
  require(bool(result) && succeeded(zkc::admitStage(*result)),
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
void extendProduct(func::FuncOp target, unsigned multiplications,
                   StringRef contract) {
  auto prototype = sf::application(target, contract);
  require(prototype.getInputs().size() == 2,
          "missing multiplication prototype");
  Value result = sc::payload(prototype).front();
  auto item = target.getArgument(1);
  for (unsigned i = 1; i < multiplications; ++i) {
    auto *next = sc::appendApply(
        target, prototype.getBinding(), ValueRange{result, item},
        TypeRange{result.getType()}, "product_" + std::to_string(i));
    result = sc::payload(next).front();
  }
  sc::returned(target).setOperand(0, result);
}
// Probe the actual comparator independently of the producer's operation order.
// The caller below separately checks the complete admission and context.
FailureOr<Value> compare(ModuleOp source, ModuleOp candidate, uint64_t &work,
                         mathematical::ComparisonCapacity &capacity) {
  auto computation = readComputation(source);
  auto view =
      take(mathematical::ScopedCandidate::read(&candidate.getBody()->front()));
  mathematical::CandidatePorts ports(view.get());
  SymbolTable symbols(&candidate.getBody()->front());
  auto target = sf::function(candidate, "work");
  auto *first = view->first(&target.front());
  Operation *cursor = first;
  while (cursor && !mathematical::hasFinitePayloadContract(cursor, symbols))
    cursor = view->next(cursor);
  require(cursor && ports.outputs(first).size() == 1,
          "candidate has no admitted cardinality or bulk payload");
  auto *saved = cursor;
  auto returned = sc::returned(target);
  llvm::DenseSet<Operation *> bindings;
  auto result = mathematical::compareFinitePayload(
      computation, target.getArguments().drop_front(),
      ports.outputs(first).front(), cursor, symbols, bindings, work, returned,
      &capacity, nullptr, view.get());
  if (failed(result))
    require(cursor == saved && bindings.empty(),
            "failed comparison published cursor or bindings");
  else
    require(cursor == returned && *result == returned.getValues().front(),
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
                  : "nested scoped readers share actual work",
        [&] {
          auto source = nestedKernelReductions(context);
          auto original = clone(*source);
          auto unit = *source->getBody()->getOps<mlir::ModuleOp>().begin();
          mathematical::RealizationWork work;
          work.requiredFiniteChecking = 1000;
          work.optionalFiniteChecking = 0;
          uint64_t copies = 1000000, bytes = 16 * 1024 * 1024;
          OwningOpRef<ModuleOp> schedule;
          auto ordered = computation::realizeEntry(
              unit, "nested", {false, false}, work, copies, bytes, {}, nullptr,
              nullptr, nullptr, false, &schedule);
          require(bool(ordered), "outer reader starved its nested callbacks");
          auto [loops, nestedLoops] = loopCounts(*ordered, "evaluate");
          require(loops == 3 && nestedLoops == 2,
                  "fixture lost its outer fold or sibling nested folds");
          auto candidate = scheduled ? std::move(schedule) : clone(*ordered);
          require(bool(candidate), "nested schedule construction refused");
          auto before = clone(*candidate);
          finite::VerificationResult outcome{
              finite::VerificationStatus::Mismatch, {}};
          auto check = [&](uint64_t localCap, uint64_t &shared) {
            finite::VerificationLimits limits{localCap, 0, &shared};
            return scheduled ? computation::verifyEntrySchedule(
                                   unit, *candidate, "nested", {false, false},
                                   limits, &outcome)
                             : computation::verifyEntryRecipes(
                                   unit, *candidate, "nested", {false, false},
                                   limits, &outcome);
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
    auto measured = computation::realizeEntry(unit, "nested", {false, false},
                                              work, copies, bytes);
    require(bool(measured), "nested construction measurement refused");
    const uint64_t cost = 1000 - work.requiredFiniteChecking;
    require(cost > 1 && cost < 1000,
            "nested construction did not share required checking work");
    work = {};
    work.requiredFiniteChecking = cost;
    work.optionalFiniteChecking = 0;
    copies = 1000000;
    bytes = 16 * 1024 * 1024;
    auto exact = computation::realizeEntry(unit, "nested", {false, false}, work,
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
        computation::realizeEntry(unit, "nested", {false, false}, work, copies,
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
    auto candidate = computation::realizeEntry(
        unit, "reductions", {}, session.work, session.remainingCopy,
        session.remainingSiteBytes, {100000, 1}, nullptr, &session);
    require(bool(candidate),
            "attributable optional retries refused ordered source");
    auto [loops, nestedLoops] = loopCounts(*candidate, "evaluate");
    require(
        loops == 2 && nestedLoops == 0 && same(*source, *before) &&
            succeeded(computation::verifyEntryRecipes(unit, *candidate,
                                                      "reductions")),
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
        auto measured = computation::realizeEntry(
            unit, "boundary", {false, false}, work, copies, bytes);
        require(bool(measured), "ordered copy measurement refused");
        uint64_t cost = 1000000 - copies;
        require(cost > 1, "ordered construction did not charge copies");
        work = {};
        copies = cost;
        bytes = 16 * 1024 * 1024;
        require(bool(computation::realizeEntry(unit, "boundary", {false, false},
                                               work, copies, bytes)) &&
                    copies == 0,
                "exact ordered copy allowance refused");
        work = {};
        copies = cost - 1;
        bytes = 16 * 1024 * 1024;
        ScopedDiagnosticHandler quiet(&context,
                                      [](Diagnostic &) { return success(); });
        require(
            !computation::realizeEntry(unit, "boundary", {false, false}, work,
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
    cases.run(name + " precise independent comparison boundary", [&] {
      auto source = fixture(context, name);
      auto candidate = sf::prepare(*source, vectorPolicy);
      auto target = sf::function(*candidate, "work");
      auto view = take(
          mathematical::ScopedCandidate::read(&candidate->getBody()->front()));
      auto result = dyn_cast_or_null<exec::ApplyOp>(
          view->producer(sc::returned(target).getValues().front()));
      require(result && result.getInputs().size() == 2,
              "fixture no longer returns a binary bulk result");
      Value left = result.getInputs()[0], right = result.getInputs()[1];
      view.reset();
      result.getInputsMutable().assign(ValueRange{right, left});
      require(succeeded(zkc::admitStage(*candidate)) &&
                  succeeded(sf::compare(*source, *candidate)),
              "commuted valid candidate was refused");
      uint64_t work = 100000;
      mathematical::ComparisonCapacity capacity;
      require(succeeded(compare(*source, *candidate, work, capacity)) &&
                  capacity == mathematical::ComparisonCapacity::None,
              "ample comparison refused");
      uint64_t cost = 100000 - work;
      require(cost > 1, "missing comparator charges");
      work = cost;
      require(succeeded(compare(*source, *candidate, work, capacity)) &&
                  work == 0 &&
                  capacity == mathematical::ComparisonCapacity::None,
              "successful exact allowance was classified as capacity");
      work = cost - 1;
      require(failed(compare(*source, *candidate, work, capacity)) &&
                  capacity == mathematical::ComparisonCapacity::Work &&
                  work == 0,
              "failed final charge did not report work capacity");
      auto checked = check(*source, *candidate, 100000, 1);
      require(checked.outcome == Observation::OptionalCapacity &&
                  checked.detail == "finite comparison work",
              "optional capacity was reported as semantic mismatch");
      llvm::outs() << name << " comparison work: " << cost << '\n';
    });
    cases.run(name + " changed result remains a hard refusal", [&] {
      auto source = fixture(context, name);
      auto candidate = sf::prepare(*source, vectorPolicy);
      auto target = sf::function(*candidate, "work");
      sc::returned(target).setOperand(0, name == "collect"
                                             ? target.getArgument(1)
                                             : target.getArguments().back());
      require(succeeded(verify(*candidate)),
              "changed result was not an ordinary well-formed candidate");
      auto checked = check(*source, *candidate);
      require(checked.outcome == Observation::Mismatch,
              "changed result was downgraded to capacity");
      std::string diagnostic;
      ScopedDiagnosticHandler capture(&context, [&](Diagnostic &d) {
        diagnostic += d.str();
        return success();
      });
      require(failed(sf::compare(*source, *candidate)) &&
                  namesIdentifier(diagnostic, "algorithm-correspondence"),
              "mismatch lost its refusal identifier");
    });
    cases.run(name + " optional capacity retries checked ordered source", [&] {
      auto source = fixture(context, name);
      mathematical::RealizationWork work;
      work.optionalFiniteChecking = 1;
      const auto initial = work;
      std::string diagnostic;
      ScopedDiagnosticHandler capture(&context, [&](Diagnostic &d) {
        diagnostic += d.str();
        return success();
      });
      auto fallback = prepare(*source, work);
      require(bool(fallback) && diagnostic.empty(),
              "transient capacity did not retry silently");
      auto ordered = sf::prepare(*source, {false, false});
      require(
          sf::hasLoop(*fallback) && same(*fallback, *ordered) &&
              succeeded(sf::compare(*source, *fallback)),
          "fallback differs from independently checked ordered realization");
      require(work.optionalFiniteChecking == 0 &&
                  work.discardedRecipeCopy < initial.discardedRecipeCopy,
              "optional retry replenished comparison or discarded copy work");
      if (name == "collect")
        require(work.lanes < initial.lanes,
                "discarded candidate replenished optional lane work");
      require(work.matching.structural < initial.matching.structural,
              "discarded candidate replenished optional matching work");
    });
    cases.run(name + " required reader boundary and atomic refusal", [&] {
      auto source = fixture(context, name);
      auto original = clone(*source);
      auto ordered = sf::prepare(*source, {false, false});
      uint64_t cost = 0;
      for (; cost < 1000; ++cost) {
        auto checked = check(*source, *ordered, cost, 0);
        if (checked.outcome == Observation::Verified)
          break;
        require(checked.outcome == Observation::RequiredCapacity &&
                    checked.detail == "finite reader work" &&
                    checked.capacity &&
                    checked.capacity->owner == WorkOwner::RequiredFiniteReader,
                "required reader exhaustion became a mismatch");
      }
      require(cost > 1 && cost < 1000, "missing ordered reader boundary");
      mathematical::RealizationWork work;
      work.requiredFiniteChecking = cost;
      work.optionalFiniteChecking = 0;
      auto exact = prepare(*source, work, {false, false});
      require(bool(exact) && work.requiredFiniteChecking == 0 &&
                  same(*exact, *ordered),
              "exact required allowance changed or refused output");
      work = {};
      work.requiredFiniteChecking = cost - 1;
      work.optionalFiniteChecking = 1;
      mathematical::VerificationDecision outcome;
      std::string diagnostic;
      ScopedDiagnosticHandler capture(&context, [&](Diagnostic &d) {
        diagnostic += d.str();
        return success();
      });
      auto refused = prepare(*source, work, vectorPolicy, &outcome);
      require(!refused && same(*source, *original) &&
                  outcome.outcome == Observation::RequiredCapacity &&
                  outcome.detail == "finite reader work" && outcome.capacity &&
                  outcome.capacity->owner == WorkOwner::RequiredFiniteReader &&
                  namesIdentifier(diagnostic, "algorithm-correspondence"),
              "required refusal published a partial source or lost its budget");
      llvm::outs() << name << " ordered reader work: " << cost << '\n';
    });
  }
  cases.run("ordinary valid formula reaches independent term depth limit", [&] {
    auto source = fixture(context, "collect");
    auto candidate = sf::prepare(*source, vectorPolicy);
    extendProduct(sf::function(*source, "square"), ring::Limits::depth,
                  "field.mul");
    extendProduct(sf::function(*candidate, "square"), ring::Limits::depth,
                  "field.mul");
    extendProduct(sf::function(*candidate, "work"), ring::Limits::depth,
                  "vector.mul");
    require(succeeded(zkc::admitStage(*source)) &&
                succeeded(zkc::admitStage(*candidate)),
            "deep equivalent formulas were not admitted");
    uint64_t work = 100000;
    mathematical::ComparisonCapacity capacity;
    require(failed(compare(*source, *candidate, work, capacity)) && work > 0 &&
                capacity == mathematical::ComparisonCapacity::Depth,
            "term depth failure was conflated with work or mismatch");
    auto checked = check(*source, *candidate);
    require(checked.outcome == Observation::OptionalCapacity &&
                checked.detail == "finite comparison term depth",
            "depth exhaustion did not reach the transaction boundary");
    auto ordered = sf::prepare(*source, {false, false});
    require(
        succeeded(sf::compare(*source, *ordered)),
        "admitted deep formula lost its independently checked ordered path");
  });
  return cases.result();
}
