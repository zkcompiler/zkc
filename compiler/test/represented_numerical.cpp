#include "../lib/Target/NumericalPlan.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Algebra/Parameters.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Support/Json.h"

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
using namespace zkc::protocol;
namespace {
void accept(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
void refuse(Error error, StringRef code) {
  require(bool(error), "expected refusal");
  require(namesIdentifier(toString(std::move(error)), code),
          "wrong refusal code");
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  ScopedDiagnosticHandler quiet(&context,
                                [](Diagnostic &) { return success(); });
  Cases cases;
  for (StringRef domain :
       {"koala-bear", "goldilocks", "bn254.fr", "bls12-381.fr",
        "ristretto255.scalar", "koala-bear.ext4-binomial3",
        "gf2-64.pentanomial-4-3-1",
        "gf2-64.pentanomial-4-3-1.ext3-trinomial1"}) {
    auto field = algebra::FieldType::get(&context, domain);
    auto logical = take(algebra::importRingExpression(
        &context,
        take(ring::Expression::create(
            {{domain.str()}, {domain.str()}},
            {ring::Node::slot(0), ring::Node::slot(1), ring::Node::mul(1, 1),
             ring::Node::add(0, 2), ring::Node::neg(3)},
            {4}))));
    for (unsigned bits : {0, 1, 2, 3}) {
      auto mask =
          DenseBoolArrayAttr::get(&context, {bool(bits & 1), bool(bits & 2)});
      cases.run(
          "actual word tile and resident schedule " + domain + "/" +
              Twine(bits),
          [&] {
            auto plan =
                take(target::proposeNumericalPlan(field, logical, mask, 8));
            accept(target::verifyNumericalPlan(field, logical, mask, plan));
            require(plan.getLanes() == 8, "actual tile extent lost");
            require(plan.getSlots() < plan.getExpression().getNodes().size(),
                    "liveness produced no storage reuse");
            auto neutral = take(runtime::exportNumericalPlan(plan));
            std::string text;
            for (bool bit : mask.asArrayRef())
              text += bit ? '1' : '0';
            accept(checkNumericalPlan(neutral, domain, text));
            // Fresh storage is another valid allocation, not the producer
            // answer.
            neutral.slots = neutral.locations.size();
            for (unsigned i = 0; i < neutral.locations.size(); ++i)
              neutral.locations[i] = i;
            auto alternative =
                take(runtime::importNumericalPlan(&context, neutral));
            accept(
                target::verifyNumericalPlan(field, logical, mask, alternative));
            // Choose an unambiguously invalid shape, independently of sharing.
            auto wrong = runtime::NumericalPlanAttr::get(
                &context, plan.getExpression(), 8, plan.getSlots(),
                DenseI32ArrayAttr::get(&context, {}));
            refuse(target::verifyNumericalPlan(field, logical, mask, wrong),
                   "numerical-plan-shape");
          });
    }
  }
  auto field = algebra::FieldType::get(&context, "koala-bear");
  auto mask = DenseBoolArrayAttr::get(&context, {true});
  auto logical = take(algebra::importRingExpression(
      &context,
      take(ring::Expression::create({{"koala-bear"}},
                                    {ring::Node::slot(0),
                                     ring::Node::literal("koala-bear", "0"),
                                     ring::Node::add(0, 1)},
                                    {2}))));
  auto plan = take(target::proposeNumericalPlan(field, logical, mask, 8));
  cases.run("actual word simplification becomes the physical expression", [&] {
    require(plan.getExpression().getNodes().size() == 1 &&
                logical.getNodes().size() == 3,
            "source expression was substituted for decoded words");
    accept(target::verifyNumericalPlan(field, logical, mask, plan));
  });
  cases.run(
      "physical and logical parameters are distinct admitted stages", [&] {
        auto args = ArrayAttr::get(
            &context, {StringAttr::get(&context, "koala-bear"), mask});
        auto native = ArrayAttr::get(&context, {plan});
        auto bytes = take(encodeInvocationParameters(
            "numerical.map", args, native, ParameterStage::Physical));
        require(take(decodeInvocationParameters("numerical.map", args, bytes,
                                                ParameterStage::Physical)) ==
                    native,
                "physical plan failed exact boundary roundtrip");
        auto old = take(algebra::encodeRingExpression(logical));
        require(!invocationParametersMatch("numerical.map", args, native, {old},
                                           ParameterStage::Physical),
                "former executable bare expression was accepted");
        auto emit = [&] { return emitError(UnknownLoc::get(&context)); };
        require(
            failed(verifyInvocationParameters(emit, "numerical.map", args,
                                              native, ParameterStage::Logical)),
            "physical plan entered the logical stage");
        require(
            failed(verifyInvocationParameters(
                emit, "numerical.map", args,
                ArrayAttr::get(&context, {logical}), ParameterStage::Physical)),
            "logical body entered the physical stage");
      });
  cases.run("changed physical semantics require fresh correspondence", [&] {
    auto different = take(algebra::importRingExpression(
        &context, take(ring::Expression::create(
                      {{"koala-bear"}},
                      {ring::Node::slot(0), ring::Node::mul(0, 0)}, {1}))));
    auto changed =
        take(target::proposeNumericalPlan(field, different, mask, 8));
    refuse(target::verifyNumericalPlan(field, logical, mask, changed),
           "represented-arithmetic");
  });
  cases.run("domain transport checks the complete source subject", [&] {
    auto foreign = take(algebra::importRingExpression(
        &context, take(ring::Expression::create({{"baby-bear"}},
                                                {ring::Node::slot(0)}, {0}))));
    refuse(target::verifyNumericalPlan(field, foreign, mask, plan),
           "numerical-body-field");
    auto empty = take(algebra::importRingExpression(
        &context, take(ring::Expression::create({}, {}, {}))));
    refuse(target::verifyNumericalPlan(field, empty, mask, plan),
           "numerical-body-signature");
  });
  cases.run("proposal reuse retains cumulative construction cost", [&] {
    uint64_t budget = target::NumericalConstructionWork;
    target::NumericalPlanProposals cache(budget);
    auto first = take(cache.propose(field, logical, mask, 8));
    auto cost = target::NumericalConstructionWork - budget;
    require(cost > 1, "construction was not charged");
    require(take(cache.propose(field, logical, mask, 8)) == first &&
                target::NumericalConstructionWork - budget == cost + 1,
            "identical immutable subject repeated lowering");
    auto changed = take(cache.propose(field, logical, mask, 4));
    require(changed.getLanes() == 4 &&
                target::NumericalConstructionWork - budget > cost + 2,
            "tile extent was absent from the reuse key");
    uint64_t exact = cost;
    target::NumericalPlanProposals exactCache(exact);
    take(exactCache.propose(field, logical, mask, 8));
    require(!exact, "exact construction budget did not settle");
    refuses(exactCache.propose(field, logical, mask, 8),
            "represented-construction-limit");
    uint64_t shortBudget = cost - 1;
    target::NumericalPlanProposals shortCache(shortBudget);
    refuses(shortCache.propose(field, logical, mask, 8),
            "represented-construction-limit");
  });
  cases.run("actual plan checks own a cumulative independent allowance", [&] {
    uint64_t budget = target::NumericalCheckingWork;
    accept(target::verifyNumericalPlan(field, logical, mask, plan, &budget));
    auto cost = target::NumericalCheckingWork - budget;
    require(cost, "independent read was not charged");
    budget = cost;
    accept(target::verifyNumericalPlan(field, logical, mask, plan, &budget));
    require(!budget, "exact checking allowance did not settle");
    refuse(target::verifyNumericalPlan(field, logical, mask, plan, &budget),
           "represented-checking-limit");
    budget = cost - 1;
    refuse(target::verifyNumericalPlan(field, logical, mask, plan, &budget),
           "represented-checking-limit");
  });
  return cases.result();
}
