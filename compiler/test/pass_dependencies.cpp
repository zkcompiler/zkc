#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Kernel/IR/KernelOps.h"
#include "zkc/Dialect/Operations.h"
#include "zkc/Interfaces/Mathematical.h"
#include "zkc/Transforms/Passes.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;

namespace {
// Register only input dialects. Parsing loads them lazily; the pass manager
// must supply any additional dialects through the pass's own declaration.
template <typename... InputDialects>
void withSource(StringRef source,
                llvm::function_ref<void(ModuleOp, MLIRContext &)> check) {
  DialectRegistry registry;
  registry.insert<protocol_ir::ProtocolDialect, InputDialects...>();
  registerMathematicalInterfaces(registry);
  MLIRContext context(registry);
  auto module = parseSourceString<ModuleOp>(source, &context);
  require(bool(module), "supported dependency fixture did not parse");
  check(*module, context);
}

void runChecked(ModuleOp module, std::unique_ptr<Pass> pass,
                ArrayRef<StringRef> createdDialects) {
  DialectRegistry dependencies;
  pass->getDependentDialects(dependencies);
  auto *context = module.getContext();
  // Fail the case before executing a pass with an uncovered dependency. In
  // particular, the preparation regression must never reach unregistered ops.
  for (auto name : createdDialects)
    require(context->getLoadedDialect(name) ||
                dependencies.getDialectAllocator(name),
            pass->getArgument() + " does not declare " + name);
  PassManager manager(context);
  manager.addPass(std::move(pass));
  require(succeeded(manager.run(module)), "pass failed after dependency check");
  require(succeeded(verify(module)), "pass produced invalid IR");
}

unsigned count(ModuleOp module, StringRef name) {
  unsigned result = 0;
  module.walk(
      [&](Operation *op) { result += op->getName().getStringRef() == name; });
  return result;
}

unsigned computationCount(ModuleOp module) {
  unsigned result = 0;
  module.walk(
      [&](Operation *op) { result += mathematical::isComputationUnit(op); });
  return result;
}

template <typename... InputDialects> std::string project(StringRef source) {
  std::string result;
  withSource<InputDialects...>(source, [&](ModuleOp module, MLIRContext &) {
    runChecked(module, protocol::createProjectProtocolPass(false),
               {"local", "algebra", "runtime"});
    llvm::raw_string_ostream stream(result);
    module.print(stream);
  });
  return result;
}

constexpr StringLiteral rangeFold = R"mlir(
module { "protocol.module"() ({
  "data.domain"() ({ ^entry(%lo: ui64, %hi: ui64):
    %d = "data.domain_range"(%lo, %hi) : (ui64, ui64) -> !data.domain<ui64>
    "data.domain_yield"(%d) : (!data.domain<ui64>) -> ()
  }) {sym_name="items", sym_visibility="private",
      function_type=(ui64, ui64) -> !data.domain<ui64>} : () -> ()
  local.func private @step(%state: i1, %item: ui64, %lo: ui64, %hi: ui64) -> i1
      attributes {logical_origin=["step", []]} {
    local.return %state : i1
  }
  "local.finite_fold"() {sym_name="fold", function_type=(ui64, ui64, i1) -> i1,
                        domain=@items, step=@step} : () -> ()
  local.func @work(%lo: ui64, %hi: ui64, %init: i1) -> i1
      attributes {logical_origin=["work", []]} {
    %r = local.apply @fold(%lo, %hi, %init) {site="fold"} : (ui64, ui64, i1) -> i1
    local.return %r : i1
  }
  "protocol.func"() ({ ^entry(%init: i1):
    %zero = "data.index"() {value="0"} : () -> ui64
    %two = "data.index"() {value="2"} : () -> ui64
    %r = "protocol.local_call"(%zero, %two, %init)
        {callee=@work, role="P", site="work"} : (ui64, ui64, i1) -> i1
    "protocol.return"(%r) : (i1) -> ()
  }) {sym_name="main", function_type=(i1) -> i1, roles=["P"],
      input_roles=[["P"]], output_roles=[["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
)mlir";

constexpr StringLiteral booleans = R"mlir(
module { "protocol.module"() ({
  "protocol.func"() ({ ^entry(%a: i1, %b: i1):
    %r = arith.andi %a, %b : i1
    "protocol.return"(%r) : (i1) -> ()
  }) {sym_name="main", function_type=(i1, i1) -> i1, roles=["P"],
      input_roles=[["P"], ["P"]], output_roles=[["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
)mlir";

constexpr StringLiteral sequence = R"mlir(
module { "protocol.module"() ({
  "protocol.func"() ({ ^entry(%a: i1):
    %empty = "data.sequence_empty"() : () -> !data.sequence<i1>
    %r = "data.sequence_append"(%empty, %a) : (!data.sequence<i1>, i1) -> !data.sequence<i1>
    "protocol.return"(%r) : (!data.sequence<i1>) -> ()
  }) {sym_name="main", function_type=(i1) -> !data.sequence<i1>, roles=["P"],
      input_roles=[["P"]], output_roles=[["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
)mlir";

constexpr StringLiteral algorithms = R"mlir(
module { "protocol.module"() ({
  local.func private @identity(%a: i1) -> i1 attributes {logical_origin=["identity", []]} {
    local.return %a : i1
  }
  local.func @work(%a: i1) -> i1 attributes {logical_origin=["work", []]} {
    %r = local.apply @identity(%a) {site="identity"} : (i1) -> i1
    local.return %r : i1
  }
  "protocol.func"() ({ ^entry(%a: i1):
    %r = "protocol.local_call"(%a) {callee=@work, role="P", site="work"} : (i1) -> i1
    "protocol.return"(%r) : (i1) -> ()
  }) {sym_name="main", function_type=(i1) -> i1, roles=["P"],
      input_roles=[["P"]], output_roles=[["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
)mlir";

constexpr StringLiteral finiteCollection = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!A = !algebra.field_array<"bls12-381.fr", 2>
module { "protocol.module"() ({
  "data.domain"() ({ ^entry(%lo: ui64, %hi: ui64):
    %d = "data.domain_range"(%lo, %hi) : (ui64, ui64) -> !data.domain<ui64>
    "data.domain_yield"(%d) : (!data.domain<ui64>) -> ()
  }) {sym_name="items", sym_visibility="private",
      function_type=(ui64, ui64) -> !data.domain<ui64>} : () -> ()
  func.func private @body(%i: ui64, %lo: ui64, %hi: ui64, %value: !F) -> !F {
    func.return %value : !F
  }
  "protocol.func"() ({ ^entry(%value: !F):
    %zero = "data.index"() {value="0"} : () -> ui64
    %two = "data.index"() {value="2"} : () -> ui64
    %r = "algebra.finite_collect"(%zero, %two, %value)
        {domain=@items, body=@body} : (ui64, ui64, !F) -> !A
    "protocol.return"(%r) : (!A) -> ()
  }) {sym_name="main", function_type=(!F) -> !A, roles=["P"],
      input_roles=[["P"]], output_roles=[["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
)mlir";

constexpr StringLiteral polynomial = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!A = !algebra.field_array<"bls12-381.fr", 2>
!P = !poly.polynomial<"bls12-381.fr", 1>
!C = !poly.polynomial<"bls12-381.fr", 0>
module { "protocol.module"() ({
  "protocol.func"() ({ ^entry(%table: !A, %point: !F):
    %p = "poly.mle"(%table) : (!A) -> !P
    %fixed = "poly.fix"(%p, %point) : (!P, !F) -> !C
    %r = "poly.evaluate"(%fixed) : (!C) -> !F
    "protocol.return"(%r) : (!F) -> ()
  }) {sym_name="main", function_type=(!A, !F) -> !F, roles=["P"],
      input_roles=[["P"], ["P"]], output_roles=[["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
)mlir";
} // namespace

int main() {
  Cases cases;
  for (bool projection : {false, true})
    cases.run(
        projection ? "project a range fold without input algebra"
                   : "prepare a range fold without input algebra",
        [&] {
          withSource<data::DataDialect, local::LocalDialect>(
              rangeFold, [&](ModuleOp module, MLIRContext &context) {
                require(!context.getLoadedDialect<algebra::AlgebraDialect>() &&
                            !context.getLoadedDialect<func::FuncDialect>(),
                        "range fixture unexpectedly loaded algebra or func");
                auto pass = projection
                                ? protocol::createProjectProtocolPass(false)
                                : protocol::createPrepareProtocolPass(false);
                runChecked(module, std::move(pass),
                           {"local", "algebra", "runtime"});
                require(
                    context.getLoadedDialect<algebra::AlgebraDialect>() &&
                        count(module, "algebra.exec.index_constant") &&
                        count(module, "algebra.exec.index_less") &&
                        count(module, "local.for") &&
                        !count(module, "local.finite_fold") &&
                        !count(module, "local.apply"),
                    "range fold was not expanded to registered execution ops");
              });
        });
  cases.run("lower booleans with no input local or algebra dialect", [&] {
    auto participant = project<arith::ArithDialect>(booleans);
    // Reparse in a fresh context so projection's dependencies cannot mask the
    // standalone lowering pass's registration obligations.
    withSource<arith::ArithDialect>(participant, [&](ModuleOp module,
                                                     MLIRContext &context) {
      require(!context.getLoadedDialect<local::LocalDialect>() &&
                  !context.getLoadedDialect<algebra::AlgebraDialect>(),
              "participant fixture unexpectedly loaded execution dialects");
      runChecked(module, protocol::createLowerMathPass(),
                 {"local", "exec", "kernel", "func"});
      require(computationCount(module) && count(module, "kernel.call") &&
                  count(module, "arith.andi") &&
                  !count(module, "algebra.exec.bool_and"),
              "logical formation executed Boolean recipes early");
      std::string logical;
      llvm::raw_string_ostream(logical) << module;
      withSource<arith::ArithDialect, local::LocalDialect,
                 kernel::KernelDialect, func::FuncDialect>(
          logical, [&](ModuleOp candidate, MLIRContext &fresh) {
            require(!fresh.getLoadedDialect<algebra::AlgebraDialect>(),
                    "Kernel fixture unexpectedly loaded recipe dialect");
            runChecked(candidate, kernel::createLowerKernelsPass(),
                       {"algebra"});
            require(count(candidate, "algebra.exec.bool_and") &&
                        !computationCount(candidate) &&
                        !count(candidate, "kernel.call") &&
                        !count(candidate, "arith.andi"),
                    "standalone Kernel pass did not execute Boolean recipes");
          });
      withSource<arith::ArithDialect, local::LocalDialect,
                 kernel::KernelDialect, func::FuncDialect>(
          logical, [&](ModuleOp candidate, MLIRContext &fresh) {
            require(!fresh.getLoadedDialect<algebra::AlgebraDialect>() &&
                        !fresh.getLoadedDialect<plan::PlanDialect>() &&
                        !fresh.getLoadedDialect<runtime::RuntimeDialect>(),
                    "Kernel fixture unexpectedly loaded physical dialects");
            runChecked(candidate, protocol::createSelectPhysicalPass(),
                       {"algebra", "plan", "runtime"});
            require(count(candidate, "plan.apply") == 1 &&
                        !count(candidate, "algebra.exec.bool_and") &&
                        !computationCount(candidate) &&
                        !count(candidate, "kernel.call"),
                    "physical pass did not realize its logical Kernel input");
          });
      require(count(module, "local.func") && count(module, "kernel.call") &&
                  count(module, "arith.andi"),
              "Boolean logical closure was not retained");
    });
  });
  cases.run("sequence recipes retain their input data dialect", [&] {
    auto participant = project<data::DataDialect>(sequence);
    withSource<data::DataDialect>(
        participant, [&](ModuleOp module, MLIRContext &context) {
          require(context.getLoadedDialect<data::DataDialect>() &&
                      !context.getLoadedDialect<local::LocalDialect>(),
                  "sequence fixture does not isolate data from local");
          runChecked(module, protocol::createLowerMathPass(),
                     {"local", "exec", "kernel", "func", "data"});
          require(count(module, "kernel.call") &&
                      count(module, "data.sequence_append") &&
                      !count(module, "data.exec.sequence_append"),
                  "sequence recipes ran during formation");
          runChecked(module, kernel::createLowerKernelsPass(),
                     {"local", "algebra", "data", "runtime"});
          require(count(module, "data.exec.sequence_empty") &&
                      count(module, "data.exec.sequence_append") &&
                      !count(module, "data.sequence_append"),
                  "sequence recipes did not execute");
        });
  });
  cases.run("algorithm expansion creates only input dialect entities", [&] {
    withSource<local::LocalDialect>(algorithms, [&](ModuleOp module,
                                                    MLIRContext &context) {
      require(count(module, "local.apply"), "missing algorithm call");
      runChecked(module, protocol::createExpandAlgorithmsPass(), {"local"});
      require(!count(module, "local.apply") && count(module, "local.return") &&
                  !context.getLoadedDialect<algebra::AlgebraDialect>() &&
                  !context.getLoadedDialect<func::FuncDialect>(),
              "algorithm expansion did not remain in its input dialects");
    });
  });
  cases.run("finite recipes use data and func already present in input", [&] {
    auto participant =
        project<algebra::AlgebraDialect, data::DataDialect, func::FuncDialect>(
            finiteCollection);
    withSource<algebra::AlgebraDialect, data::DataDialect, func::FuncDialect>(
        participant, [&](ModuleOp module, MLIRContext &context) {
          require(context.getLoadedDialect<data::DataDialect>() &&
                      context.getLoadedDialect<func::FuncDialect>() &&
                      !context.getLoadedDialect<local::LocalDialect>() &&
                      count(module, "func.func"),
                  "finite fixture lost its source helper or loaded local");
          runChecked(module, protocol::createLowerMathPass(),
                     {"local", "exec", "kernel", "data", "func"});
          require(count(module, "kernel.call") &&
                      count(module, "algebra.finite_collect") &&
                      count(module, "data.domain") &&
                      !count(module, "local.for"),
                  "finite raw closure was not retained");
          runChecked(module, kernel::createLowerKernelsPass(),
                     {"local", "algebra", "data", "func", "runtime"});
          require(count(module, "local.for") &&
                      count(module, "algebra.exec.field_array_from_vector") &&
                      !count(module, "algebra.finite_collect") &&
                      !count(module, "func.func") &&
                      !count(module, "data.domain"),
                  "finite recipe did not lower and consume its source helper");
        });
  });
  for (bool eliminate : {false, true})
    cases.run(
        eliminate ? "eliminate polynomials into nominal array operations"
                  : "fix polynomial factors in their input dialects",
        [&] {
          auto participant =
              project<algebra::AlgebraDialect, poly::PolynomialDialect>(
                  polynomial);
          withSource<algebra::AlgebraDialect, poly::PolynomialDialect>(
              participant, [&](ModuleOp module, MLIRContext &context) {
                require(count(module, "poly.fix"),
                        "missing polynomial observation");
                auto pass = eliminate
                                ? protocol::createEliminatePolynomialsPass()
                                : protocol::createFixPolynomialFactorsPass();
                runChecked(module, std::move(pass), {"algebra", "poly"});
                require(
                    !count(module, "poly.fix") &&
                        !context.getLoadedDialect<data::DataDialect>() &&
                        !context.getLoadedDialect<func::FuncDialect>(),
                    "polynomial rewrite did not remain in its input dialects");
                require(eliminate ? !count(module, "poly.evaluate") &&
                                        count(module, "algebra.array_at")
                                  : count(module, "poly.fix_table"),
                        "polynomial recipe did not execute");
              });
        });
  return cases.result();
}
