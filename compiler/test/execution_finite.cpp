#include "mlir/IR/Verifier.h"
#include "mlir/Interfaces/CallInterfaces.h"
#include "mlir/Interfaces/LoopLikeInterface.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/Execution.h"
#include <tuple>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
constexpr llvm::StringLiteral fold = R"mlir(
!S = !runtime.scope
!F = !algebra.field<"koala-bear">
!V = !algebra.field_vector<"koala-bear">
!O = !exec.outcome<(!F)>
module {
 "data.domain"() ({ ^entry(%v:!V):
   %d = "data.domain_indices"(%v) {axis=0:i64} : (!V)->!data.domain<ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<ui64>} : ()->()
 func.func private @step(%scope:!S,%state:!F,%i:ui64,%domain:!V,%capture:!V,%flag:i1)->!O
     attributes {no_inline, runtime.origin=["step",[]], data.preconditions=[#data.index_bound<2,3,0>,#data.index_bound<2,4,0>,#data.equal_extent<3,0,4,0>]} {
   cf.cond_br %flag, ^keep, ^stop
 ^keep:
   %ok = "exec.returned"(%state) : (!F)->!O
   return %ok : !O
 ^stop:
   %cause = "exec.reject"(%scope) {reason="callback",site="stop"} : (!S)->!exec.stop
   %failed = "exec.failed"(%cause) : (!exec.stop)->!O
   return %failed : !O
 }
 func.func private @predicate(%scope:!S,%i:ui64,%domain:!V,%capture:!V,%flag:i1)->!exec.outcome<(i1)>
     attributes {no_inline, runtime.origin=["predicate",[]]} {
   %ok = "exec.returned"(%flag) : (i1)->!exec.outcome<(i1)>
   return %ok : !exec.outcome<(i1)>
 }
 func.func @caller(%scope:!S,%domain:!V,%seed:!F,%capture:!V,%flag:i1)->!O
     attributes {no_inline,runtime.origin=["caller",[]],data.preconditions=[#data.equal_extent<1,0,3,0>]} {
   %outcome = "exec.fold"(%scope,%domain,%seed,%capture,%flag) {domain=@items,step=@step,predicate=@predicate,site="fold"} : (!S,!V,!F,!V,i1)->!O
   "exec.dispatch"(%outcome)[^done,^failed] : (!O)->()
 ^done(%value:!F):
   %ok = "exec.returned"(%value) : (!F)->!O
   return %ok : !O
 ^failed(%cause:!exec.stop):
   %failed = "exec.failed"(%cause) : (!exec.stop)->!O
   return %failed : !O
 }
})mlir";
constexpr llvm::StringLiteral collect = R"mlir(
!S = !runtime.scope
!F = !algebra.field<"koala-bear">
!V = !algebra.field_vector<"koala-bear">
!O = !exec.outcome<(!V)>
module {
 "data.domain"() ({ ^entry(%v:!V):
   %d = "data.domain_elements"(%v) : (!V)->!data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 func.func private @body(%scope:!S,%item:!F,%domain:!V)->!exec.outcome<(!F)>
     attributes {no_inline,runtime.origin=["body",[]]} {
   %ok = "exec.returned"(%item) : (!F)->!exec.outcome<(!F)>
   return %ok : !exec.outcome<(!F)>
 }
 func.func @caller(%scope:!S,%domain:!V)->!O
     attributes {no_inline,runtime.origin=["caller",[]]} {
   %outcome = "exec.collect"(%scope,%domain) {domain=@items,body=@body,site="collect"} : (!S,!V)->!O
   "exec.dispatch"(%outcome)[^done,^failed] : (!O)->()
 ^done(%value:!V):
   %ok = "exec.returned"(%value) : (!V)->!O
   return %ok : !O
 ^failed(%cause:!exec.stop):
   %failed = "exec.failed"(%cause) : (!exec.stop)->!O
   return %failed : !O
 }
})mlir";
std::string changed(StringRef text, StringRef before, StringRef after) {
  auto result = text.str();
  auto at = result.find(before.str());
  require(at != std::string::npos, "missing mutation target");
  result.replace(at, before.size(), after.str());
  return result;
}
Operation *occurrence(ModuleOp module) {
  Operation *result = nullptr;
  module.lookupSymbol<func::FuncOp>("caller").walk([&](Operation *op) {
    if (isa<exec::FoldOp, exec::CollectOp>(op))
      result = op;
  });
  require(result != nullptr, "missing finite occurrence");
  return result;
}
template <typename Check>
void refuses(MLIRContext &context, StringRef identifier, Check check) {
  std::string diagnostic;
  ScopedDiagnosticHandler handler(&context, [&](Diagnostic &value) {
    diagnostic += value.str();
    return success();
  });
  require(failed(check()), "invalid finite occurrence accepted");
  require(namesIdentifier(diagnostic, identifier),
          "unexpected refusal: " + diagnostic);
}
} // namespace
int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto parse = [&](StringRef text) {
    auto module =
        parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
    require(bool(module), "fixture did not parse");
    return module;
  };
  auto accept = [&](StringRef text) {
    auto module = parse(text);
    require(succeeded(verify(*module)), "formed occurrence refused");
    require(succeeded(finite::verifyClosure(*module)),
            "finite closure refused");
    for (auto function : module->getOps<func::FuncOp>())
      require(succeeded(runtime::verifyScopeOwnership(function)),
              "scope borrowing refused");
    return module;
  };
  auto admit = [&](ModuleOp module) {
    if (auto error = protocol::verifySourceExecutionClosure(module))
      throw std::runtime_error(llvm::toString(std::move(error)));
  };
  auto refuseAdmission = [&](ModuleOp module, StringRef code) {
    auto error = protocol::verifySourceExecutionClosure(module);
    require(bool(error), "invalid source closure admitted");
    auto diagnostic = llvm::toString(std::move(error));
    require(namesIdentifier(diagnostic, code),
            "unexpected admission refusal: " + diagnostic);
  };
  cases.run(
      "source admission checks the complete ordered collection closure", [&] {
        auto module = accept(collect);
        admit(*module);
        zkc::test::refuses(protocol::readSourceExecutionDefinitions(*module),
                           "execution-cfg");
        module->lookupSymbol<func::FuncOp>("body")->removeAttr(
            "runtime.origin");
        refuseAdmission(*module, "execution-cfg");
      });
  cases.run("finite formation alone does not admit an arbitrary callback CFG",
            [&] {
              auto module = accept(fold);
              refuseAdmission(*module, "execution-cfg");
            });
  cases.run("source admission checks unused finite callback bodies", [&] {
    auto module = accept(collect);
    auto extra =
        cast<func::FuncOp>(module->lookupSymbol<func::FuncOp>("body")->clone());
    extra.setSymName("unused");
    extra->removeAttr("no_inline");
    module->getBody()->push_back(extra);
    refuseAdmission(*module, "execution-cfg");
  });
  cases.run("affine finite state needs scoped root preservation", [&] {
    auto text = changed(
        collect, "!O = !exec.outcome<(!V)>",
        "!T = !runtime.capability<\"transcript:merlin3.bls12-381.fr64be/0\">\n"
        "!O = !exec.outcome<(!T)>");
    text = changed(text,
                   "@body(%scope:!S,%item:!F,%domain:!V)->!exec.outcome<(!F)>",
                   "@body(%scope:!S,%state:!T,%item:!F,%domain:!V)->!O");
    text = changed(text, "\"exec.returned\"(%item) : (!F)->!exec.outcome<(!F)>",
                   "\"exec.returned\"(%state) : (!T)->!O");
    text = changed(text, "return %ok : !exec.outcome<(!F)>", "return %ok : !O");
    text = changed(text, "@caller(%scope:!S,%domain:!V)",
                   "@caller(%scope:!S,%domain:!V,%seed:!T)");
    text = changed(text, "\"exec.collect\"(%scope,%domain)",
                   "\"exec.fold\"(%scope,%domain,%seed)");
    text = changed(text, "body=@body", "step=@body");
    text = changed(text, "(!S,!V)->!O", "(!S,!V,!T)->!O");
    text = changed(text, "^done(%value:!V)", "^done(%value:!T)");
    text = changed(text, "\"exec.returned\"(%value) : (!V)->!O",
                   "\"exec.returned\"(%value) : (!T)->!O");
    auto module = accept(text);
    refuseAdmission(*module, "execution-cfg");
  });
  cases.run("actual scoped fold ABI and exact positional aliases", [&] {
    auto module = accept(fold);
    auto *op = occurrence(*module);
    finite::Computation c;
    require(succeeded(finite::describe(op, c)) && c.scoped && !c.total &&
                !c.collect && c.arguments == 1 && c.states == 1 &&
                c.captures == 2,
            "logical finite partitions changed");
    auto callback = finite::readCallbackABI(c, finite::CallbackRole::Step);
    require(succeeded(callback) && callback->scope &&
                callback->signature.getNumInputs() == 6 &&
                callback->formals.state[0] == callback->entry->getArgument(1) &&
                callback->formals.items[0] == callback->entry->getArgument(2),
            "scope was treated as an ordinary data port");
    auto parts = finite::partitionEntry(c, op->getOperands().drop_front());
    require(succeeded(parts), "entry partition refused");
    SmallVector<Value> alias{parts->domain[0], parts->captures[1]};
    auto binding = finite::bindCallback(
        *callback,
        {parts->initialState, callback->formals.items, parts->domain, alias},
        op->getOperand(0));
    require(succeeded(binding) && binding->actuals.size() == 6 &&
                *binding->lookup(cast<BlockArgument>(callback->scope)) ==
                    op->getOperand(0) &&
                binding->actuals[3] == binding->actuals[4] &&
                binding->actuals[1] == parts->initialState[0],
            "scope, state or aliased formal position lost");
    require(failed(finite::bindCallback(*callback, callback->formals)) &&
                failed(finite::bindCallback(*callback, callback->formals,
                                            parts->initialState[0])) &&
                failed(finite::readCallback(c, finite::CallbackRole::Step)),
            "scoped CFG became an unscoped call or expression");
    auto predicate =
        finite::readCallbackABI(c, finite::CallbackRole::Predicate);
    require(succeeded(predicate) && predicate->formals.state.empty() &&
                failed(finite::bindCallback(*predicate, callback->formals,
                                            op->getOperand(0))),
            "predicate acquired fold state");
    require(isa<SymbolUserOpInterface>(op) && !isa<CallOpInterface>(op) &&
                !isa<LoopLikeOpInterface>(op) && !isMemoryEffectFree(op) &&
                !isSpeculatable(op),
            "retained finite request claimed an invalid interface");
  });
  cases.run(
      "collect callback returns an element rather than the collection", [&] {
        auto module = accept(collect);
        finite::Computation c;
        require(succeeded(finite::describe(occurrence(*module), c)),
                "description");
        auto callback = finite::readCallbackABI(c, finite::CallbackRole::Body);
        require(
            c.scoped && c.collect && c.states == 0 && succeeded(callback) &&
                cast<exec::OutcomeType>(callback->signature.getResult(0))
                        .getPayload()[0] != c.signature.getResult(0) &&
                failed(finite::readCallbackABI(c, finite::CallbackRole::Step)),
            "collection result became callback state");
      });
  for (auto [name, before, after] :
       {std::tuple{"missing callback", "step=@step", "step=@missing"},
        {"missing domain", "domain=@items", "domain=@missing"},
        {"wrong callback kind", "step=@step", "step=@items"},
        {"public callback", "private @step", "@step"},
        {"wrong predicate", "predicate=@predicate", "predicate=@step"},
        {"empty occurrence", "site=\"fold\"", "site=\"\""},
        {"unsupported attribute", "site=\"fold\"",
         "site=\"fold\",trusted=true"},
        {"outlined callback", "runtime.origin=[\"step\",[]]",
         "runtime.origin=[\"step\",[]],runtime.region"}})
    cases.run(name, [&, before = before, after = after] {
      auto module = parse(changed(fold, before, after));
      refuses(context, "finite-formation", [&] { return verify(*module); });
    });
  cases.run("callback assumptions use the actual scoped entry indices", [&] {
    auto module = parse(
        changed(fold, "#data.index_bound<2,3,0>", "#data.index_bound<1,3,0>"));
    refuses(context, "finite-bound", [&] { return verify(*module); });
  });
  cases.run("capture bounds require actual occurrence extent evidence", [&] {
    auto module = parse(changed(fold, "#data.equal_extent<1,0,3,0>",
                                "#data.equal_extent<1,0,1,0>"));
    refuses(context, "finite-bound", [&] { return verify(*module); });
  });
  cases.run(
      "entry assumptions do not transfer to same-numbered successors", [&] {
        auto text =
            changed(fold, "   %outcome = \"exec.fold\"",
                    "   cf.br ^invoke(%scope,%domain,%seed,%capture,%flag : "
                    "!S,!V,!F,!V,i1)\n"
                    " ^invoke(%s:!S,%d:!V,%v:!F,%c:!V,%b:i1):\n"
                    "   %outcome = \"exec.fold\"");
        text =
            changed(text, "\"exec.fold\"(%scope,%domain,%seed,%capture,%flag)",
                    "\"exec.fold\"(%scope,%d,%v,%c,%b)");
        auto module = parse(text);
        refuses(context, "finite-bound", [&] { return verify(*module); });
      });
  cases.run("scope must be the owning function's exact borrowed scope", [&] {
    auto module = accept(fold);
    occurrence(*module)->setOperand(
        0, module->lookupSymbol<func::FuncOp>("step").getArgument(0));
    refuses(context, "finite-formation",
            [&] { return finite::verifyLocal(occurrence(*module)); });
  });
  cases.run(
      "fixed collection cardinality comes from the actual domain input", [&] {
        auto text = changed(collect, "!F = !algebra.field<\"koala-bear\">",
                            "!F = !algebra.field<\"bls12-381.fr\">");
        text = changed(text, "!V = !algebra.field_vector<\"koala-bear\">",
                       "!V = !algebra.field_array<\"bls12-381.fr\", 2>");
        auto module = accept(text);
        auto *op = occurrence(*module);
        auto wrong = parseSourceString<ModuleOp>(
            "module { func.func private @types() -> !exec.outcome<"
            "(!algebra.field_array<\"bls12-381.fr\", 3>)> }",
            &context);
        require(bool(wrong), "wrong-cardinality type fixture");
        op->getResult(0).setType(
            wrong->lookupSymbol<func::FuncOp>("types").getResultTypes()[0]);
        refuses(context, "finite-formation",
                [&] { return finite::verify(op); });
      });
  cases.run("malformed sibling domain is refused before typed inspection", [&] {
    auto module = accept(collect);
    auto domain = module->lookupSymbol<data::DomainOp>("items");
    domain->setAttr("function_type",
                    TypeAttr::get(IntegerType::get(&context, 1)));
    refuses(context, "finite-formation", [&] {
      finite::Computation c;
      return finite::describe(occurrence(*module), c);
    });
  });
  cases.run("all potential finite callback references must be acyclic", [&] {
    auto text = changed(
        fold, "   cf.cond_br %flag, ^keep, ^stop",
        "   %again = func.call @caller(%scope,%domain,%state,%capture,%flag) : "
        "(!S,!V,!F,!V,i1)->!O\n   cf.cond_br %flag, ^keep, ^stop");
    auto module = parse(text);
    require(succeeded(verify(*module)), "cycle fixture is malformed");
    refuses(context, "finite-cycle",
            [&] { return finite::verifyClosure(*module); });
  });
  cases.run("zero-state folds retain an ordered outcome and callback", [&] {
    auto text =
        changed(collect, "!O = !exec.outcome<(!V)>", "!O = !exec.outcome<>");
    text = changed(text,
                   "@body(%scope:!S,%item:!F,%domain:!V)->!exec.outcome<(!F)>",
                   "@body(%scope:!S,%item:!F,%domain:!V)->!O");
    text = changed(text, "\"exec.returned\"(%item) : (!F)->!exec.outcome<(!F)>",
                   "\"exec.returned\"() : ()->!O");
    text = changed(text, "return %ok : !exec.outcome<(!F)>", "return %ok : !O");
    text = changed(text, "\"exec.collect\"", "\"exec.fold\"");
    text = changed(text, "body=@body", "step=@body");
    text = changed(text, "^done(%value:!V):", "^done:");
    text = changed(text, "\"exec.returned\"(%value) : (!V)->!O",
                   "\"exec.returned\"() : ()->!O");
    auto module = accept(text);
    admit(*module);
    finite::Computation c;
    require(succeeded(finite::describe(occurrence(*module), c)) && !c.collect &&
                c.states == 0 && c.signature.getNumResults() == 0,
            "zero state became collection or missing outcome");
    auto callback = finite::readCallbackABI(c, finite::CallbackRole::Step);
    require(succeeded(callback) && callback->formals.state.empty() &&
                callback->formals.items.size() == 1 &&
                failed(finite::readCallback(c, finite::CallbackRole::Step)),
            "empty result made an ordered callback total");
  });
  cases.run("ordered outcomes do not use a mathematical result summary", [&] {
    auto module = accept(fold);
    finite::Summary summary;
    refuses(context, "finite-formation",
            [&] { return finite::summarize(occurrence(*module), summary); });
    auto extracted = protocol::readSourceExecutionDefinitions(*module);
    require(!extracted, "unrealized finite call escaped executable extraction");
    llvm::consumeError(extracted.takeError());
  });
  return cases.result();
}
