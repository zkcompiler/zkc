#include "support/NativeCases.h"
#include "zkc/Contracts/Numerical.h"
#include "zkc/Support/Json.h"

using namespace llvm;
using namespace zkc;
using namespace zkc::test;
using namespace zkc::protocol;
namespace {
NumericalPlan example() {
  return {take(ring::Expression::create(
              {{"bn254.fr"}, {"bn254.fr"}},
              {ring::Node::slot(0), ring::Node::slot(1), ring::Node::mul(1, 1),
               ring::Node::add(0, 2), ring::Node::mul(3, 3)},
              {4})),
          8,
          2,
          {1, 0, 0, 1, 1}};
}
void accept(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
void reject(Error error, StringRef code) {
  require(bool(error), "expected refusal " + code);
  require(namesIdentifier(toString(std::move(error)), code),
          "wrong schedule refusal code");
}
} // namespace
int main() {
  Cases cases;
  for (StringRef mask : {"00", "01", "10", "11"})
    cases.run("reused scratch slots for mask " + mask, [&] {
      auto plan = example();
      // With x invariant and y varying, x must persist across every chunk.
      if (mask == "01") {
        plan.slots = 3;
        plan.locations = {0, 1, 1, 2, 2};
      }
      accept(checkNumericalPlan(plan, "bn254.fr", mask));
      auto bytes = printJson(plan.encode());
      auto read = take(readNumericalPlan(bytes, "bn254.fr", mask));
      require(printJson(read.encode()) == bytes && read.slots == plan.slots,
              "physical plan lost exact canonical identity");
    });
  cases.run("separate fresh slots are another admitted schedule", [&] {
    auto plan = example();
    plan.slots = 5;
    plan.locations = {0, 1, 2, 3, 4};
    accept(checkNumericalPlan(plan, "bn254.fr", "10"));
  });
  cases.run("persistent capture cannot be overwritten", [&] {
    auto plan = example();
    plan.locations.back() = 0;
    reject(checkNumericalPlan(plan, "bn254.fr", "10"),
           "numerical-plan-schedule");
  });
  cases.run("a later operand cannot read an overwritten value", [&] {
    auto plan = example();
    plan.slots = 1;
    plan.locations = {0, 0, 0, 0, 0};
    reject(checkNumericalPlan(plan, "bn254.fr", "11"),
           "numerical-plan-schedule");
  });
  cases.run("nonempty scratch shape", [&] {
    auto plan = example();
    plan.slots = 0;
    reject(checkNumericalPlan(plan, "bn254.fr", "10"), "numerical-plan-shape");
  });
  cases.run("no undeclared scratch slots", [&] {
    auto plan = example();
    plan.locations[0] = 2;
    reject(checkNumericalPlan(plan, "bn254.fr", "10"), "numerical-plan-shape");
  });
  cases.run("no unused allocated slots", [&] {
    auto plan = example();
    plan.slots = 3;
    reject(checkNumericalPlan(plan, "bn254.fr", "10"), "numerical-plan-shape");
  });
  cases.run("every node has an actual location", [&] {
    auto plan = example();
    plan.locations.pop_back();
    reject(checkNumericalPlan(plan, "bn254.fr", "10"), "numerical-plan-shape");
  });
  for (unsigned lanes : {0, 257})
    cases.run("bounded nonempty tile " + Twine(lanes), [&] {
      auto plan = example();
      plan.lanes = lanes;
      reject(checkNumericalPlan(plan, "bn254.fr", "10"),
             "numerical-plan-shape");
    });
  cases.run("nominal field is retained", [&] {
    reject(checkNumericalPlan(example(), "bls12-381.fr", "10"),
           "numerical-body-field");
  });
  cases.run("mask is not inferred from live expression inputs", [&] {
    reject(checkNumericalPlan(example(), "bn254.fr", "1"),
           "numerical-body-signature");
    reject(checkNumericalPlan(example(), "bn254.fr", "1x"), "numerical-mask");
  });
  cases.run("former executable bare expression is refused", [&] {
    refuses(readNumericalPlan(printJson(example().expression.encode()),
                              "bn254.fr", "10"),
            "numerical-plan");
  });
  cases.run("canonical plan bytes are required", [&] {
    refuses(readNumericalPlan(" " + printJson(example().encode()), "bn254.fr",
                              "10"),
            "numerical-plan-canonical");
  });
  cases.run("plan carrier has an independent capacity", [&] {
    refuses(readNumericalPlan(std::string(NumericalLimits::planBytes + 1, ' '),
                              "bn254.fr", "10"),
            "numerical-plan-bytes");
  });
  return cases.result();
}
