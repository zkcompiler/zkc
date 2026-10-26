#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Operations.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
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

unsigned boundCount(ModuleOp module, StringRef contract,
                    bool physical = false) {
  unsigned result = 0;
  module.walk([&](exec::ApplyOp op) {
    auto binding = dyn_cast_or_null<runtime::BindingOp>(
        SymbolTable::lookupNearestSymbolFrom(op, op.getBindingAttr()));
    result += binding && binding.getContract() == contract &&
              (!physical || !binding.getImplementation().empty());
  });
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
               {"exec", "algebra", "runtime", "func", "cf", "arith"});
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
  func.func private @step(%scope: !runtime.scope, %state: i1, %item: ui64, %lo: ui64, %hi: ui64) -> !exec.outcome<(i1)>
      attributes {no_inline, runtime.origin=["step", []]} {
    %r = "exec.returned"(%state) : (i1) -> !exec.outcome<(i1)>
    return %r : !exec.outcome<(i1)>
  }
  func.func @work(%scope: !runtime.scope, %lo: ui64, %hi: ui64, %init: i1) -> !exec.outcome<(i1)>
      attributes {no_inline, runtime.origin=["work", []]} {
    %r = "exec.fold"(%scope, %lo, %hi, %init) {domain=@items, step=@step, site="fold"}
        : (!runtime.scope, ui64, ui64, i1) -> !exec.outcome<(i1)>
    "exec.dispatch"(%r)[^returned, ^stopped] : (!exec.outcome<(i1)>) -> ()
  ^returned(%value: i1):
    %done = "exec.returned"(%value) : (i1) -> !exec.outcome<(i1)>
    return %done : !exec.outcome<(i1)>
  ^stopped(%stop: !exec.stop):
    %failed = "exec.failed"(%stop) : (!exec.stop) -> !exec.outcome<(i1)>
    return %failed : !exec.outcome<(i1)>
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
  func.func private @identity(%scope: !runtime.scope, %a: i1) -> !exec.outcome<(i1)>
      attributes {no_inline, runtime.origin=["identity", []]} {
    %r = "exec.returned"(%a) : (i1) -> !exec.outcome<(i1)>
    return %r : !exec.outcome<(i1)>
  }
  func.func @work(%scope: !runtime.scope, %a: i1) -> !exec.outcome<(i1)>
      attributes {no_inline, runtime.origin=["work", []]} {
    %r = func.call @identity(%scope, %a) {runtime.site="identity"}
        : (!runtime.scope, i1) -> !exec.outcome<(i1)>
    "exec.dispatch"(%r)[^returned, ^stopped] : (!exec.outcome<(i1)>) -> ()
  ^returned(%value: i1):
    %done = "exec.returned"(%value) : (i1) -> !exec.outcome<(i1)>
    return %done : !exec.outcome<(i1)>
  ^stopped(%stop: !exec.stop):
    %failed = "exec.failed"(%stop) : (!exec.stop) -> !exec.outcome<(i1)>
    return %failed : !exec.outcome<(i1)>
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
          withSource<data::DataDialect, runtime::RuntimeDialect,
                     exec::ExecDialect, func::FuncDialect>(
              rangeFold, [&](ModuleOp module, MLIRContext &context) {
                require(!context.getLoadedDialect<algebra::AlgebraDialect>(),
                        "range fixture unexpectedly loaded algebra");
                auto pass = projection
                                ? protocol::createProjectProtocolPass(false)
                                : protocol::createPrepareProtocolPass(false);
                runChecked(
                    module, std::move(pass),
                    {"exec", "algebra", "runtime", "func", "cf", "arith"});
                require(count(module, "exec.fold") &&
                            count(module, "data.domain"),
                        "source preparation erased the finite request");
                if (!projection)
                  runChecked(module, protocol::createProjectProtocolPass(false),
                             {"exec", "runtime", "func", "cf", "arith"});
                runChecked(module, protocol::createLowerMathPass(),
                           {"exec", "runtime", "func", "cf", "arith"});
                runChecked(module, protocol::createSelectPhysicalPass(),
                           {"exec", "runtime", "func", "cf", "arith"});
                require(count(module, "exec.range") &&
                            count(module, "cf.cond_br") &&
                            !count(module, "exec.fold") &&
                            !count(module, "data.domain"),
                        "physical selection did not realize the ordered range");
              });
        });
  cases.run("lower booleans with no input execution dialects", [&] {
    auto participant = project<arith::ArithDialect>(booleans);
    // A fresh context prevents projection's dependencies from masking the
    // standalone lowering pass's registration obligations.
    withSource<arith::ArithDialect>(participant, [&](ModuleOp module,
                                                     MLIRContext &context) {
      require(!context.getLoadedDialect<exec::ExecDialect>() &&
                  !context.getLoadedDialect<runtime::RuntimeDialect>(),
              "participant fixture unexpectedly loaded execution dialects");
      runChecked(module, protocol::createLowerMathPass(),
                 {"exec", "runtime", "func", "cf", "arith"});
      require(computationCount(module) && count(module, "exec.compute") &&
                  count(module, "arith.andi") && !count(module, "exec.apply"),
              "logical formation executed Boolean recipes early");
      std::string logical;
      llvm::raw_string_ostream(logical) << module;
      for (bool physical : {false, true})
        withSource<arith::ArithDialect, exec::ExecDialect,
                   runtime::RuntimeDialect, func::FuncDialect>(
            logical, [&](ModuleOp candidate, MLIRContext &) {
              auto pass = physical ? protocol::createSelectPhysicalPass()
                                   : kernel::createLowerKernelsPass();
              runChecked(candidate, std::move(pass),
                         {"exec", "runtime", "func", "cf", "arith"});
              require(boundCount(candidate, "bool.and", physical) == 1 &&
                          !computationCount(candidate) &&
                          !count(candidate, "exec.compute") &&
                          !count(candidate, "arith.andi"),
                      "standalone pass did not realize the Boolean contract");
            });
      require(computationCount(module) && count(module, "exec.compute") &&
                  count(module, "arith.andi"),
              "Boolean logical closure was not retained");
    });
  });
  cases.run("sequence recipes retain their input data dialect", [&] {
    auto participant = project<data::DataDialect>(sequence);
    withSource<data::DataDialect>(
        participant, [&](ModuleOp module, MLIRContext &context) {
          require(context.getLoadedDialect<data::DataDialect>() &&
                      !context.getLoadedDialect<exec::ExecDialect>(),
                  "sequence fixture does not isolate data from execution");
          runChecked(module, protocol::createLowerMathPass(),
                     {"exec", "runtime", "func", "cf", "arith", "data"});
          require(count(module, "exec.compute") &&
                      count(module, "data.sequence_append") &&
                      !count(module, "exec.apply"),
                  "sequence recipes ran during formation");
          runChecked(module, kernel::createLowerKernelsPass(),
                     {"exec", "runtime", "func", "cf", "arith", "data"});
          require(boundCount(module, "sequence.empty") &&
                      boundCount(module, "sequence.append") &&
                      !count(module, "data.sequence_append"),
                  "sequence recipes did not execute");
        });
  });
  cases.run("demand lowering expands scoped ordinary helpers", [&] {
    auto participant =
        project<exec::ExecDialect, runtime::RuntimeDialect, func::FuncDialect>(
            algorithms);
    withSource<exec::ExecDialect, runtime::RuntimeDialect, func::FuncDialect>(
        participant, [&](ModuleOp module, MLIRContext &) {
          require(count(module, "func.call"), "missing ordinary helper call");
          runChecked(module, protocol::createLowerMathPass(),
                     {"exec", "runtime", "func", "cf", "arith"});
          require(!count(module, "func.call") && count(module, "exec.returned"),
                  "scoped helper call was not expanded");
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
                      !context.getLoadedDialect<exec::ExecDialect>() &&
                      count(module, "func.func"),
                  "finite fixture lost its source helper or loaded execution");
          runChecked(module, protocol::createLowerMathPass(),
                     {"exec", "runtime", "func", "cf", "arith", "data"});
          require(count(module, "exec.compute") &&
                      count(module, "algebra.finite_collect") &&
                      count(module, "data.domain") &&
                      !count(module, "exec.range"),
                  "finite raw closure was not retained");
          runChecked(module, kernel::createLowerKernelsPass(),
                     {"exec", "runtime", "func", "cf", "arith", "data"});
          require(count(module, "exec.range") && count(module, "cf.cond_br") &&
                      boundCount(module, "field_array.from_vector") &&
                      !count(module, "algebra.finite_collect") &&
                      !computationCount(module) &&
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
