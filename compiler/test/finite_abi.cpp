#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
using namespace mlir;
using namespace zkc;
using namespace zkc::finite;
using namespace zkc::test;
namespace {
const char *source = R"mlir(
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%lo:ui64,%hi:ui64):
   %r = "data.domain_range"(%lo,%hi) : (ui64,ui64)->!data.domain<ui64>
   %d = "data.domain_product"(%r,%r) : (!data.domain<ui64>,!data.domain<ui64>)->!data.domain<ui64,ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64,ui64>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(ui64,ui64)->!data.domain<ui64,ui64>} : ()->()
 func.func private @step(%a:ui64,%b:ui64,%i:ui64,%j:ui64,%lo:ui64,%hi:ui64,%x:ui64,%y:ui64)->(ui64,ui64) {
   func.return %b,%x : ui64,ui64
 }
 func.func private @predicate(%i:ui64,%j:ui64,%lo:ui64,%hi:ui64,%x:ui64,%y:ui64)->i1 {
   %yes = arith.constant true
   func.return %yes : i1
 }
 func.func private @body(%i:ui64,%j:ui64,%lo:ui64,%hi:ui64,%x:ui64,%y:ui64)->ui64 {
   func.return %j : ui64
 }
 func.func private @fold(%lo:ui64,%hi:ui64,%a:ui64,%b:ui64,%x:ui64,%y:ui64)->(ui64,ui64) {
   %r:2 = "algebra.finite_fold"(%lo,%hi,%a,%b,%x,%y) {domain=@items,step=@step,predicate=@predicate} : (ui64,ui64,ui64,ui64,ui64,ui64)->(ui64,ui64)
   func.return %r#0,%r#1 : ui64,ui64
 }
 func.func private @collect(%lo:ui64,%hi:ui64,%x:ui64,%y:ui64)->!algebra.indices {
   %r = "algebra.finite_collect"(%lo,%hi,%x,%y) {domain=@items,body=@body,predicate=@predicate} : (ui64,ui64,ui64,ui64)->!algebra.indices
   func.return %r : !algebra.indices
 }
 func.func private @stop(%scope:!runtime.scope,%i:ui64,%j:ui64,%lo:ui64,%hi:ui64,%x:ui64,%y:ui64)->!exec.outcome<> attributes {no_inline,runtime.origin=["stop",[]]} {
   %reason = "exec.reject"(%scope) {site="stop",reason="abort"} : (!runtime.scope)->!exec.stop
   cf.br ^failed(%reason : !exec.stop)
 ^failed(%cause:!exec.stop):
   %r = "exec.failed"(%cause) : (!exec.stop)->!exec.outcome<>
   func.return %r : !exec.outcome<>
 }
 func.func private @empty(%scope:!runtime.scope,%i:ui64,%j:ui64,%lo:ui64,%hi:ui64,%x:ui64,%y:ui64)->!exec.outcome<> attributes {no_inline,runtime.origin=["empty",[]]} {
   %r = "exec.returned"() : ()->!exec.outcome<>
   func.return %r : !exec.outcome<>
 }
 func.func private @zero(%scope:!runtime.scope,%lo:ui64,%hi:ui64,%x:ui64,%y:ui64)->!exec.outcome<> attributes {no_inline,runtime.origin=["zero",[]]} {
   %r = "exec.fold"(%scope,%lo,%hi,%x,%y) {domain=@items,step=@stop,site="fold"} : (!runtime.scope,ui64,ui64,ui64,ui64)->!exec.outcome<>
   "exec.dispatch"(%r)[^ok,^failed] : (!exec.outcome<>)->()
 ^ok:
   %done = "exec.returned"() : ()->!exec.outcome<>
   func.return %done : !exec.outcome<>
 ^failed(%reason:!exec.stop):
   %failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<>
   func.return %failure : !exec.outcome<>
 }
 "protocol.func"() ({ ^entry(%x:ui64):
   "protocol.return"(%x) : (ui64)->()
 }) {sym_name="main",function_type=(ui64)->ui64,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
}
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto module = parseSourceString<ModuleOp>(source, &context);
  require(bool(module), "ABI fixture admission failed");
  auto *unit = &module->getBody()->front();
  SymbolTableCollection symbols;
  auto describeSymbol = [&](StringRef name) {
    Computation c;
    require(succeeded(describe(
                &cast<func::FuncOp>(SymbolTable::lookupSymbolIn(unit, name))
                     .front()
                     .front(),
                c, unit, &symbols)),
            "cannot describe callback");
    return c;
  };
  Cases cases;
  cases.run("same-typed positions and normal result order", [&] {
    auto c = describeSymbol("fold");
    auto callback = readCallback(c, CallbackRole::Step);
    require(succeeded(callback), "step ABI refused");
    const auto &f = callback->abi.formals;
    require(f.state.size() == 2 && f.items.size() == 2 &&
                f.domain.size() == 2 && f.captures.size() == 2,
            "partition mismatch");
    SmallVector<Value> invocation{f.domain[0], f.domain[1],   f.state[0],
                                  f.state[1],  f.captures[0], f.captures[1]};
    auto entry = partitionEntry(c, invocation);
    require(succeeded(entry) && entry->initialState[0] == f.state[0] &&
                entry->captures[1] == f.captures[1],
            "entry order changed");
    auto env = bindCallback(callback->abi, {entry->initialState, f.items,
                                            entry->domain, entry->captures});
    require(succeeded(env), "binding refused");
    for (auto formal : callback->abi.entry->getArguments())
      require(*env->lookup(formal) == formal, "same type collapsed a position");
    require(callback->exit == CallbackExit::Return &&
                callback->returned[0] == f.state[1] &&
                callback->returned[1] == f.captures[0],
            "return order lost");
  });
  cases.run("aliases retain formals and current state is not seed", [&] {
    auto c = describeSymbol("fold");
    auto callback = readCallback(c, CallbackRole::Step);
    require(succeeded(callback), "step ABI refused");
    auto f = callback->abi.formals;
    SmallVector<Value> repeated{f.state[0], f.state[0]};
    auto env =
        bindCallback(callback->abi, {f.state, f.items, repeated, repeated});
    require(succeeded(env) && env->actuals.size() == 8, "aliases collapsed");
    require(*env->lookup(cast<BlockArgument>(f.domain[0])) == f.state[0] &&
                *env->lookup(cast<BlockArgument>(f.captures[1])) ==
                    f.state[0] &&
                *env->lookup(cast<BlockArgument>(f.state[1])) == f.state[1],
            "alias or state correspondence changed");
    require(failed(env->lookup(c.domain.getBody().front().getArgument(0))),
            "foreign formal accepted");
  });
  cases.run("predicate excludes state and checks exact typed segments", [&] {
    auto c = describeSymbol("fold");
    auto step = readCallback(c, CallbackRole::Step);
    auto predicate = readCallback(c, CallbackRole::Predicate);
    require(succeeded(step) && succeeded(predicate), "callback refused");
    auto f = step->abi.formals;
    auto env =
        bindCallback(predicate->abi, {{}, f.items, f.domain, f.captures});
    require(succeeded(env) && env->actuals.front() == f.items[0] &&
                predicate->abi.formals.state.empty(),
            "predicate got state");
    require(failed(bindCallback(predicate->abi, f)),
            "predicate accepted state");
    require(
        failed(bindCallback(step->abi, {{}, f.items, f.domain, f.captures})),
        "step accepted missing state");
    SmallVector<Value> wrong{predicate->returned[0], f.domain[1]};
    require(
        failed(bindCallback(predicate->abi, {{}, f.items, wrong, f.captures})),
        "nominal type mismatch accepted");
    require(failed(partitionEntry(c, f.items)),
            "entry arity mismatch accepted");
    SmallVector<Value> wrongEntry{f.domain[0],   f.domain[1],
                                  f.state[0],    f.state[1],
                                  f.captures[0], predicate->returned[0]};
    require(failed(partitionEntry(c, wrongEntry)),
            "entry type mismatch accepted");
  });
  cases.run("collect item is distinct from collection result", [&] {
    auto c = describeSymbol("collect");
    auto body = readCallback(c, CallbackRole::Body);
    require(succeeded(body) && body->abi.formals.state.empty() &&
                body->returned[0] == body->abi.formals.items[1] &&
                body->abi.signature.getResult(0) != c.signature.getResult(0),
            "collect item treated as collection state");
    require(failed(readCallback(c, CallbackRole::Step)),
            "collect accepted step");
    require(failed(readCallback(describeSymbol("fold"), CallbackRole::Body)),
            "fold accepted body");
  });
  cases.run("zero-state scoped stop and fresh reread after helper change", [&] {
    auto c = describeSymbol("zero");
    auto callback = readCallbackABI(c, CallbackRole::Step);
    require(succeeded(callback) && !c.collect && c.states == 0 &&
                callback->scope && failed(readCallback(c, CallbackRole::Step)),
            "scoped stop became an empty total returned expression");
    auto closure = take(protocol::readSourceExecutionClosure(unit));
    auto find = [&](StringRef name) -> const program::Function & {
      auto found = llvm::find_if(closure.definitions.functions,
                                 [&](const auto &f) { return f.name == name; });
      require(found != closure.definitions.functions.end(),
              "missing scoped callback");
      return *found;
    };
    require(std::holds_alternative<program::Stop>(
                find("stop").body.front().value) &&
                std::holds_alternative<program::Return>(
                    find("empty").body.front().value),
            "scoped admission confused stopping and empty return");
    c.operation->setAttr("step", FlatSymbolRefAttr::get(&context, "empty"));
    c = describeSymbol("zero");
    auto fresh = readCallbackABI(c, CallbackRole::Step);
    require(succeeded(fresh) && fresh->formals.state.empty() &&
                fresh->symbol != callback->symbol &&
                failed(readCallback(c, CallbackRole::Step)),
            "reread retained stale helper or granted a total expression");
    require(succeeded(mlir::verify(*module)),
            "replacement did not remain admitted");
  });
  cases.run("ABI inspection does not weaken finite body admission", [&] {
    auto c = describeSymbol("fold");
    auto callback = readCallback(c, CallbackRole::Step);
    require(succeeded(callback), "original callback refused");
    auto *terminator = callback->terminator;
    SmallVector<Value> original(terminator->getOperands());
    terminator->setOperands(ValueRange{});
    bool inspectable = succeeded(readCallbackABI(c, CallbackRole::Step));
    bool expressionRefused = failed(readCallback(c, CallbackRole::Step));
    std::string diagnostic;
    bool admissionRefused;
    {
      ScopedDiagnosticHandler handler(&context, [&](Diagnostic &value) {
        diagnostic += value.str();
        return success();
      });
      admissionRefused = failed(finite::verify(c.operation));
    }
    terminator->setOperands(original);
    require(inspectable && expressionRefused && admissionRefused &&
                namesIdentifier(diagnostic, "finite-formation"),
            "inspectable ports granted malformed-body admission");
  });
  cases.run("CFG ABI does not imply a single returned expression", [&] {
    auto c = describeSymbol("fold");
    auto original = readCallbackABI(c, CallbackRole::Step);
    require(succeeded(original), "original ABI refused");
    auto helper =
        func::FuncOp::create(module->getLoc(), "cfg_step", original->signature);
    helper.setPrivate();
    module->getBody()->push_back(helper);
    auto *entry = helper.addEntryBlock();
    auto *tail = new Block();
    helper.getBody().push_back(tail);
    for (Type type : original->signature.getInputs())
      tail->addArgument(type, helper.getLoc());
    OpBuilder builder(&context);
    builder.setInsertionPointToEnd(entry);
    cf::BranchOp::create(builder, helper.getLoc(), tail, entry->getArguments());
    builder.setInsertionPointToEnd(tail);
    func::ReturnOp::create(
        builder, helper.getLoc(),
        ValueRange{tail->getArgument(1), tail->getArgument(6)});
    require(succeeded(mlir::verify(helper)), "CFG fixture is malformed");
    c.total = true;
    c.helper = helper;
    auto abi = readCallbackABI(c, CallbackRole::Step);
    require(succeeded(abi) && abi->entry == entry &&
                abi->formals.state[0] == entry->getArgument(0),
            "CFG entry ABI refused or guessed from a successor");
    require(failed(readCallback(c, CallbackRole::Step)),
            "CFG was treated as one returned expression");
    auto env = bindCallback(*abi, abi->formals);
    require(succeeded(env) &&
                *env->lookup(entry->getArgument(0)) == entry->getArgument(0) &&
                failed(env->lookup(tail->getArgument(0))),
            "same-numbered successor became an entry formal");
    // ABI formation is not body, closure or totality admission. A current
    // expression view must inspect the actual terminator even in one block.
    entry->back().erase();
    tail->erase();
    builder.setInsertionPointToEnd(entry);
    func::ReturnOp::create(builder, helper.getLoc(), ValueRange{});
    require(succeeded(readCallbackABI(c, CallbackRole::Step)) &&
                failed(readCallback(c, CallbackRole::Step)),
            "ABI granted an invalid returned-expression view");
    helper.erase();
  });
  return cases.result();
}
