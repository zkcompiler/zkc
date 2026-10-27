#include "mlir/AsmParser/AsmParser.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Interfaces/CallInterfaces.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Analysis/TotalClosure.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/Execution.h"
#include "zkc/Dialect/Runtime/Execution.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
constexpr llvm::StringLiteral source = R"mlir(
!S = !runtime.scope
!F = !algebra.field<"koala-bear">
!O = !exec.outcome<(!F)>
module {
  func.func private @sum(%a: !F, %b: !F) -> !F {
    %v = algebra.field_add %a, %b : (!F, !F) -> !F
    return %v : !F
  }
  func.func private @product(%a: !F, %b: !F) -> !F {
    %v = algebra.field_multiply %a, %b : (!F, !F) -> !F
    return %v : !F
  }
  module @selected attributes {exec.computation} {
    func.func @entry(%a: !F, %b: !F) -> !F {
      %v = algebra.field_multiply %a, %b : (!F, !F) -> !F
      return %v : !F
    }
  }
  func.func @caller(%scope: !S, %a: !F, %b: !F) -> !O {
    %call = "exec.compute"(%scope, %a, %b) {callee = @sum, site = "sum"} : (!S, !F, !F) -> !O
    "exec.dispatch"(%call)[^done, ^failed] : (!O) -> ()
  ^done(%v: !F):
    %result = "exec.returned"(%v) : (!F) -> !O
    return %result : !O
  ^failed(%cause: !exec.stop):
    %failure = "exec.failed"(%cause) : (!exec.stop) -> !O
    return %failure : !O
  }
})mlir";
constexpr llvm::StringLiteral participant = R"mlir(
!S = !runtime.scope
!F = !algebra.field<"bls12-381.fr">
!O = !exec.outcome<(!F)>
module { "protocol.module"() <{profile = #protocol.profile<participant>}> ({
  func.func private @twice(%x: !F) -> !F {
    %v = algebra.field_add %x, %x : (!F, !F) -> !F
    return %v : !F
  }
  func.func private @entry(%x: !F) -> !F {
    %v = func.call @twice(%x) : (!F) -> !F
    return %v : !F
  }
  func.func @work(%scope: !S, %x: !F) -> !O
      attributes {no_inline, runtime.origin = ["work", []]} {
    %call = "exec.compute"(%scope, %x) {callee = @entry, site = "numerical"} : (!S, !F) -> !O
    "exec.dispatch"(%call)[^done, ^failed] : (!O) -> ()
  ^done(%v: !F):
    %result = "exec.returned"(%v) : (!F) -> !O
    return %result : !O
  ^failed(%cause: !exec.stop):
    %failure = "exec.failed"(%cause) : (!exec.stop) -> !O
    return %failure : !O
  }
  "protocol.participant"() ({
  ^entry(%x: !F):
    %v = "protocol.local_call"(%x) {callee = @work, role = "P", site = "work"} : (!F) -> !F
    "protocol.finish"(%v) : (!F) -> ()
  }) {sym_name = "endpoint", function_type = (!F) -> !F, instance = "main", role = "P"} : () -> ()
  "protocol.entry"() {sym_name = "main", targets = [["P", @endpoint]]} : () -> ()
  "protocol.projection"() {calculations = [], interfaces = [{
    source = "main", entry = @main, original_type = (!F) -> !F, roles = ["P"],
    input_roles = [["P"]], output_roles = [["P"]], statements = [],
    participants = [{participant = @endpoint, role = "P", inputs = [0:i64], service_inputs = [], outputs = [0:i64]}],
    actions = [{site = "work", kind = "protocol.local_call", callee = @work,
                targets = [{participant = @endpoint, operation = "protocol.local_call"}]}]
  }]} : () -> ()
}) : () -> () }
)mlir";
constexpr llvm::StringLiteral bounded = R"mlir(
!S = !runtime.scope
!F = !algebra.field<"koala-bear">
!V = !algebra.field_vector<"koala-bear">
!O = !exec.outcome<(!F)>
module {
  func.func private @load(%left: !V, %right: !V, %i: ui64) -> !F
      attributes {data.preconditions = [#data.index_bound<2,0,0>, #data.equal_extent<0,0,1,0>]} {
    %v = "data.bounded_at"(%left, %i) : (!V, ui64) -> !F
    return %v : !F
  }
  func.func @caller(%scope: !S, %left: !V, %right: !V, %unrelated: !V, %i: ui64, %j: ui64, %condition: i1) -> !O
      attributes {data.preconditions = [#data.index_bound<4,1,0>, #data.equal_extent<1,0,2,0>]} {
    cf.cond_br %condition, ^invoke, ^via
  ^via:
    cf.br ^invoke
  ^invoke:
    %call = "exec.compute"(%scope, %left, %right, %i) {callee = @load, site = "load"} : (!S, !V, !V, ui64) -> !O
    "exec.dispatch"(%call)[^done, ^failed] : (!O) -> ()
  ^done(%v: !F):
    %result = "exec.returned"(%v) : (!F) -> !O
    return %result : !O
  ^failed(%cause: !exec.stop):
    %failure = "exec.failed"(%cause) : (!exec.stop) -> !O
    return %failure : !O
  }
})mlir";
std::string changed(StringRef input, StringRef from, StringRef to) {
  std::string result = input.str();
  auto at = result.find(from.str());
  require(at != std::string::npos, "missing mutation target");
  result.replace(at, from.size(), to.str());
  return result;
}
exec::ComputeOp call(ModuleOp module) {
  exec::ComputeOp result;
  module.lookupSymbol<func::FuncOp>("caller").walk(
      [&](exec::ComputeOp invocation) { result = invocation; });
  require(bool(result), "missing mathematical invocation");
  return result;
}
template <typename Check>
void refuses(StringRef code, MLIRContext &context, Check check) {
  std::string diagnostic;
  ScopedDiagnosticHandler handler(&context, [&](Diagnostic &value) {
    diagnostic += value.str();
    return success();
  });
  require(failed(check()), "invalid invocation accepted");
  require(namesIdentifier(diagnostic, code),
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
    require(succeeded(verify(*module)), "valid invocation refused");
    require(succeeded(runtime::verifyScopeOwnership(
                module->lookupSymbol<func::FuncOp>("caller"))),
            "invocation did not borrow its scope");
    return module;
  };
  for (bool policy : {false, true})
    cases.run(
        policy ? "scoped participant numerical selection policy"
               : "scoped participant numerical admission",
        [&] {
          auto module = parse(participant);
          exec::ComputeOp request;
          module->walk([&](exec::ComputeOp op) { request = op; });
          require(bool(request), "missing participant computation");
          if (policy) {
            OpBuilder builder(&context);
            request.setPolicyAttr(
                builder.getBoolArrayAttr({true, false, false}));
          }
          require(succeeded(verify(*module)),
                  "scoped participant numerical source refused");
          auto closure = take(protocol::readSourceExecutionClosure(
              &module->getBody()->front()));
          require(closure.bodies.at("work").front().operation == request &&
                      !isMemoryEffectFree(request) && !isSpeculatable(request),
                  "participant numerical invocation lost source identity or "
                  "ordered semantics");
        });
  cases.run("actual source body and ordered adapter interfaces", [&] {
    auto module = accept(source);
    SymbolTableCollection symbols;
    auto invocation = call(*module);
    require(invocation.resolveCallee(symbols) ==
                module->lookupSymbol<func::FuncOp>("sum"),
            "actual helper identity lost");
    require(isa<SymbolUserOpInterface>(invocation.getOperation()) &&
                !isa<CallOpInterface>(invocation.getOperation()) &&
                !isMemoryEffectFree(invocation) && !isSpeculatable(invocation),
            "ordered scope/outcome adapter claimed an inappropriate interface");
    invocation.setCalleeAttr(SymbolRefAttr::get(&context, "product"));
    require(succeeded(verify(*module)) &&
                invocation.resolveCallee(symbols) ==
                    module->lookupSymbol<func::FuncOp>("product"),
            "resolution cached a previous target");
  });
  cases.run("actual selected public entry", [&] {
    auto module =
        accept(changed(source, "callee = @sum", "callee = @selected::@entry"));
    auto unit = module->lookupSymbol<ModuleOp>("selected");
    SymbolTableCollection symbols;
    require(succeeded(mathematical::verifyComputationUnit(unit)) &&
                call(*module).resolveCallee(symbols) ==
                    unit.lookupSymbol<func::FuncOp>("entry"),
            "selected entry identity lost");
  });
  cases.run("upstream symbol rename updates actual invocation", [&] {
    auto module = accept(source);
    auto helper = module->lookupSymbol<func::FuncOp>("sum");
    require(succeeded(SymbolTable::replaceAllSymbolUses(
                helper, StringAttr::get(&context, "renamed"), *module)),
            "symbol use rewrite failed");
    helper.setSymName("renamed");
    require(succeeded(verify(*module)) &&
                call(*module).getCalleeAttr().getRootReference() == "renamed",
            "typed invocation did not participate in symbol rewriting");
  });
  cases.run(
      "nested symbol tables do not borrow an outer mathematical helper", [&] {
        auto module = accept(source);
        auto inner = ModuleOp::create(module->getLoc(), "inner");
        module->getBody()->push_back(inner);
        inner.getBody()->push_back(
            module->lookupSymbol<func::FuncOp>("caller").clone());
        refuses("execution-computation-symbol", context,
                [&] { return verify(*module); });
        auto helper = module->lookupSymbol<func::FuncOp>("sum").clone();
        inner.getBody()->push_back(helper);
        SymbolTableCollection symbols;
        require(succeeded(verify(*module)) &&
                    call(inner).resolveCallee(symbols) == helper,
                "nested invocation did not resolve its own actual helper");
      });
  for (unsigned mask = 0; mask < 8; ++mask)
    cases.run("selection choices " + std::to_string(mask), [&] {
      auto module = parse(source);
      OpBuilder builder(&context);
      call(*module).setPolicyAttr(builder.getBoolArrayAttr(
          {bool(mask & 1), bool(mask & 2), bool(mask & 4)}));
      require(succeeded(verify(*module)), "valid policy refused");
    });
  auto reject = [&](StringRef name, StringRef from, StringRef to,
                    StringRef code) {
    cases.run(name.str(), [&] {
      auto module = parse(changed(source, from, to));
      refuses(code, context, [&] { return verify(*module); });
    });
  };
  reject("missing helper", "callee = @sum", "callee = @absent",
         "execution-computation-symbol");
  reject("public source helper", "private @sum", "@sum",
         "execution-computation-symbol");
  reject("external source helper", R"mlir({
    %v = algebra.field_add %a, %b : (!F, !F) -> !F
    return %v : !F
  })mlir",
         "", "execution-computation-symbol");
  reject("missing occurrence", "site = \"sum\"", "site = \"\"",
         "execution-formation");
  reject("unknown attribute", "site = \"sum\"", "site = \"sum\", extra = true",
         "execution-computation-attribute");
  reject("short policy", "site = \"sum\"", "site = \"sum\", policy = [true]",
         "execution-computation-policy");
  reject("nonboolean policy", "site = \"sum\"",
         "site = \"sum\", policy = [true, false, 1 : i64]",
         "execution-computation-policy");
  reject("actual arity", "@sum(%a: !F, %b: !F)", "@sum(%a: !F, %b: !F, %c: !F)",
         "execution-computation-signature");
  reject("different result type", "!O = !exec.outcome<(!F)>",
         "!O = !exec.outcome<(i64)>", "execution-computation-signature");
  reject("unknown nested entry", "callee = @sum", "callee = @selected::@absent",
         "execution-computation-symbol");
  reject("too-deep reference", "callee = @sum",
         "callee = @selected::@entry::@x", "execution-computation-symbol");
  reject("flat reference cannot select module", "callee = @sum",
         "callee = @selected", "execution-computation-symbol");
  reject("nested reference cannot select function", "callee = @sum",
         "callee = @product::@entry", "execution-computation-symbol");
  cases.run("selected entry must be public and profiled", [&] {
    for (StringRef mutation : {"private @entry", "@entry"}) {
      auto text =
          changed(source, "callee = @sum", "callee = @selected::@entry");
      text = mutation.starts_with("private")
                 ? changed(text, "@entry(%a", "private @entry(%a")
                 : changed(text, "attributes {exec.computation}", "");
      auto module = parse(text);
      refuses("execution-computation-symbol", context,
              [&] { return verify(*module); });
    }
  });
  cases.run("mathematical ports exclude represented and capability types", [&] {
    for (StringRef type :
         {"!runtime.scope", "!exec.stop",
          "!runtime.transfer<(!algebra.field<\"koala-bear\">)>",
          "!runtime.represented<!algebra.field<\"koala-bear\">, "
          "\"plonky3.koala-bear/0\">"}) {
      // Inspect the operation before unrelated helper/CFG shape checks run.
      auto module = parse(source);
      auto port = parseType(type, &context);
      require(bool(port), "invalid test port type");
      call(*module).getInputs().front().setType(port);
      refuses("execution-computation-signature", context,
              [&] { return call(*module).verify(); });
      module = parse(source);
      call(*module).getOutcome().setType(
          exec::OutcomeType::get(&context, {port}));
      refuses("execution-computation-signature", context,
              [&] { return call(*module).verify(); });
    }
  });
  cases.run("formal mathematical source ports remain logical", [&] {
    for (StringRef type :
         {"!poly.polynomial<\"koala-bear\", 1>", "!poly.quotient<12289, 8>"}) {
      auto module = parse(source);
      auto port = parseType(type, &context);
      require(bool(port), "invalid formal test type");
      call(*module).getInputs().front().setType(port);
      require(succeeded(call(*module).verify()), "logical formal port refused");
    }
  });
  cases.run("call cannot borrow another argument as its active scope", [&] {
    auto module = parse(source);
    auto invocation = call(*module);
    auto other = invocation.getInputs().front();
    other.setType(invocation.getScope().getType());
    invocation.setOperand(0, other);
    refuses("execution-computation-context", context,
            [&] { return invocation.verify(); });
  });
  cases.run(
      "target body and raw signature checked before region admission", [&] {
        for (unsigned mutation = 0; mutation < 3; ++mutation) {
          auto module = parse(source);
          auto helper = module->lookupSymbol<func::FuncOp>("sum");
          if (mutation == 0)
            helper->setAttr("function_type",
                            TypeAttr::get(IntegerType::get(&context, 1)));
          else if (mutation == 1)
            helper.front().back().erase();
          else
            helper->setAttr("runtime.origin", UnitAttr::get(&context));
          SymbolTableCollection symbols;
          refuses(mutation == 0 ? "execution-computation-signature"
                                : "execution-computation-symbol",
                  context,
                  [&] { return call(*module).verifySymbolUses(symbols); });
        }
      });
  cases.run("formation does not publish unresolved mathematics", [&] {
    auto module = accept(source);
    auto read = protocol::readExecutionDefinitions(*module, false);
    require(!read, "prepared native reader accepted unresolved mathematics");
    llvm::consumeError(read.takeError());
    auto sourceRead = protocol::readSourceExecutionDefinitions(*module);
    require(!sourceRead,
            "scoped source reader bypassed its missing math consumer");
    llvm::consumeError(sourceRead.takeError());
  });
  cases.run("formation does not certify recursive mathematical bodies", [&] {
    auto text =
        changed(source, "algebra.field_add %a, %b", "func.call @sum(%a, %b)");
    auto module = accept(text);
    auto helper = module->lookupSymbol<func::FuncOp>("sum");
    SymbolTableCollection symbols;
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    const mathematical::TotalSummary *summary = nullptr;
    require(
        failed(
            mathematical::TotalClosure(*module, symbols).get(helper, summary)),
        "formation bypassed the mathematical closure owner");
  });
  cases.run("CFG call premises use exact data inputs after the scope", [&] {
    auto module = accept(bounded);
    auto helper = module->lookupSymbol<func::FuncOp>("load");
    auto caller = module->lookupSymbol<func::FuncOp>("caller");
    require(succeeded(finite::verifyPreconditions(caller)) &&
                succeeded(finite::verifyCallPreconditions(call(*module))) &&
                succeeded(
                    finite::verifyDefinitionClosure(*module, {helper, caller})),
            "actual data-premise mapping or complete closure check failed");
    // Equal-extent facts legitimately transfer the bound to the other vector.
    auto invocation = call(*module);
    invocation.setOperand(1, caller.getArgument(2));
    require(succeeded(finite::verifyCallPreconditions(invocation)),
            "valid equal-extent bound transfer was lost");
  });
  auto invalidPremise = [&](StringRef name, StringRef from, StringRef to) {
    cases.run(name.str(), [&] {
      auto module = accept(changed(bounded, from, to));
      refuses("finite-bound", context,
              [&] { return finite::verifyCallPreconditions(call(*module)); });
      refuses("finite-bound", context, [&] {
        return finite::verifyDefinitionClosure(
            *module, {module->lookupSymbol<func::FuncOp>("load"),
                      module->lookupSymbol<func::FuncOp>("caller")});
      });
    });
  };
  invalidPremise("unrelated same-typed container",
                 "(%scope, %left, %right, %i)",
                 "(%scope, %unrelated, %right, %i)");
  invalidPremise("unrelated same-typed index", "(%scope, %left, %right, %i)",
                 "(%scope, %left, %right, %j)");
  invalidPremise("callee bound cannot become a caller assumption",
                 "#data.index_bound<4,1,0>, ", "");
  invalidPremise("callee extent cannot become a caller assumption",
                 ", #data.equal_extent<1,0,2,0>", "");
  cases.run(
      "CFG successor arguments do not inherit entry premise indices", [&] {
        auto text = changed(bounded, "^invoke, ^via",
                            "^invoke(%unrelated, %j : !V, ui64), ^via");
        text = changed(text, "cf.br ^invoke",
                       "cf.br ^invoke(%left, %i : !V, ui64)");
        text =
            changed(text, "^invoke:", "^invoke(%selected: !V, %index: ui64):");
        text = changed(text, "(%scope, %left, %right, %i)",
                       "(%scope, %selected, %right, %index)");
        auto module = accept(text);
        refuses("finite-bound", context,
                [&] { return finite::verifyCallPreconditions(call(*module)); });
      });
  cases.run("premise checker refuses an unresolved mathematical target", [&] {
    auto module =
        parse(changed(bounded, "callee = @load", "callee = @missing"));
    refuses("finite-bound", context,
            [&] { return finite::verifyCallPreconditions(call(*module)); });
  });
  cases.run("malformed precondition carrier cannot mean no premises", [&] {
    auto module = accept(bounded);
    module->lookupSymbol<func::FuncOp>("load")->setAttr(
        "data.preconditions", UnitAttr::get(&context));
    refuses("finite-bound", context,
            [&] { return finite::verifyCallPreconditions(call(*module)); });
  });

  for (StringRef mutation :
       {"entry visibility", "helper visibility", "entry signature",
        "external entry", "empty block", "multiple blocks", "missing return"})
    cases.run(
        "safe early selected call admission with malformed " + mutation, [&] {
          auto module = parse(
              changed(source, "callee = @sum", "callee = @selected::@entry"));
          auto unit = module->lookupSymbol<ModuleOp>("selected");
          auto entry = unit.lookupSymbol<func::FuncOp>("entry");
          if (mutation == "entry visibility") {
            entry->setAttr("sym_visibility",
                           StringAttr::get(&context, "invalid"));
          } else if (mutation == "helper visibility") {
            // Every dormant member of the selected unit is admitted by its
            // owner.
            auto helper = module->lookupSymbol<func::FuncOp>("sum").clone();
            helper->setAttr("sym_visibility",
                            StringAttr::get(&context, "invalid"));
            unit.getBody()->push_back(helper);
          } else if (mutation == "entry signature") {
            entry->setAttr("function_type",
                           TypeAttr::get(IntegerType::get(&context, 64)));
          } else if (mutation == "external entry") {
            entry.getBody().getBlocks().clear();
          } else if (mutation == "multiple blocks") {
            entry.getBody().push_back(new Block());
          } else {
            entry.getBody().front().back().erase();
            if (mutation == "empty block")
              entry.getBody().front().front().erase();
          }
          SymbolTableCollection symbols;
          refuses(
              mutation == "entry signature" ? "execution-computation-signature"
                                            : "execution-computation-symbol",
              context, [&] { return call(*module).verifySymbolUses(symbols); });
        });
  for (StringRef attribute : {"arg_attrs=[{}]", "res_attrs=[{}]",
                              "arg_attrs=[{assume=true}]", "res_attrs=[]"})
    reject(
        ("adapter refuses ordinary call port dictionaries " + attribute).str(),
        "site = \"sum\"", ("site = \"sum\", " + attribute).str(),
        "execution-computation-attribute");
  for (StringRef policy :
       {"[]", "[true,false]", "[true,false,true,false]", "[1:i64,false,true]",
        "[true,0:i64,false]", "[\"true\",false,true]"})
    reject(("malformed selection choices " + policy).str(), "site = \"sum\"",
           ("site = \"sum\",policy=" + policy).str(),
           "execution-computation-policy");
  cases.run("adapter cannot use a different nominal field", [&] {
    auto module = parse(source);
    call(*module).getInputs().front().setType(
        parseType("!algebra.field<\"bls12-381.fr\">", &context));
    SymbolTableCollection symbols;
    refuses("execution-computation-signature", context,
            [&] { return call(*module).verifySymbolUses(symbols); });
  });
  cases.run("mathematical invocation requires its owner's borrowed scope", [&] {
    auto module = parse(source);
    auto caller = module->lookupSymbol<func::FuncOp>("caller");
    auto another = caller.getBody().front().addArgument(
        runtime::ScopeType::get(&context), caller.getLoc());
    call(*module).getScopeMutable().assign(another);
    refuses("execution-computation-context", context,
            [&] { return call(*module).verify(); });
  });
  cases.run("module scope is not an invocation context", [&] {
    auto module = parse(source);
    auto invocation = call(*module);
    invocation->moveBefore(&module->getBody()->front());
    refuses("execution-computation-context", context,
            [&] { return invocation.verify(); });
  });
  cases.run("return-only numerical entry", [&] {
    auto module = parse(R"mlir(
module {
  module @empty attributes {exec.computation} { func.func @entry() {func.return} }
  func.func @caller(%scope:!runtime.scope)->!exec.outcome<> {
    %call="exec.compute"(%scope) {callee=@empty::@entry,site="empty"} : (!runtime.scope)->!exec.outcome<>
    func.return %call : !exec.outcome<>
  }
})mlir");
    require(succeeded(verify(*module)), "zero-port computation refused");
  });

  auto closureSource = changed(
      source, "-> !O {",
      "-> !O attributes {no_inline, runtime.origin=[\"caller\", []]} {");
  auto checkClosure = [&](StringRef text, bool valid) {
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    auto module = parse(text);
    auto checked = protocol::verifySourceExecutionClosure(*module);
    if (valid) {
      if (checked)
        throw std::runtime_error(llvm::toString(std::move(checked)));
    } else {
      require(bool(checked), "invalid source closure accepted");
      require(namesIdentifier(llvm::toString(std::move(checked)),
                              "execution-source-closure"),
              "wrong source closure refusal");
    }
    return module;
  };
  cases.run(
      "source closure admits actual mathematical calls before realization",
      [&] {
        auto module = checkClosure(closureSource, true);
        auto native = protocol::readSourceExecutionDefinitions(*module);
        require(!native, "unresolved math escaped through native extraction");
        llvm::consumeError(native.takeError());
        auto executable = protocol::readLocalExecution(*module, false);
        require(!executable, "unresolved math escaped executable admission");
        llvm::consumeError(executable.takeError());
      });
  cases.run("source closure admits a selected unit's actual entry", [&] {
    checkClosure(
        changed(closureSource, "callee = @sum", "callee = @selected::@entry"),
        true);
  });
  cases.run(
      "source closure is rechecked after actual mathematical body mutation",
      [&] {
        auto module = checkClosure(closureSource, true);
        auto helper = module->lookupSymbol<func::FuncOp>("sum");
        OpBuilder builder(helper.getBody().front().getTerminator());
        func::CallOp::create(builder, helper.getLoc(), "sum",
                             helper.getResultTypes(), helper.getArguments());
        auto checked = protocol::verifySourceExecutionClosure(*module);
        require(bool(checked), "recursive post-check helper accepted");
        llvm::consumeError(std::move(checked));
      });
  cases.run("unused nested units still require the computation profile", [&] {
    auto module = parse(changed(participant, "  func.func private @twice",
                                "  module @unclassified {func.func @entry() "
                                "{func.return}}\n  func.func private @twice"));
    refuses("computation-profile", context, [&] { return verify(*module); });
  });
  cases.run("unused external mathematical helpers are refused", [&] {
    checkClosure(
        changed(closureSource, "  func.func @caller",
                "  func.func private @external()\n  func.func @caller"),
        false);
  });
  cases.run("logical computations cannot be published as an executable", [&] {
    auto module = parse(participant);
    require(succeeded(verify(*module)), "participant control refused");
    auto read = protocol::readExecutionModel(*module);
    require(!read, "unresolved numerical call escaped executable publication");
    llvm::consumeError(read.takeError());
  });
  cases.run("physical profile refuses a dormant logical unit", [&] {
    auto module = parse(R"mlir(module {
      "protocol.module"() ({ module @unused attributes {exec.computation} {
        func.func @entry() { func.return }
      } }) {profile=#protocol.profile<physical>} : ()->()
    })mlir");
    refuses("kernel-profile", context, [&] { return verify(*module); });
  });
  cases.run("source closure checks dormant selected units", [&] {
    checkClosure(
        changed(
            closureSource,
            "%v = algebra.field_multiply %a, %b : (!F, !F) -> !F\n      return",
            "%v = func.call @entry(%a, %b) : (!F, !F) -> !F\n      return"),
        false);
  });
  cases.run(
      "source closure checks dormant selected IR before typed inspection", [&] {
        auto module = checkClosure(closureSource, true);
        auto selected = module->lookupSymbol<ModuleOp>("selected");
        selected.lookupSymbol<func::FuncOp>("entry")->setAttr(
            "function_type", TypeAttr::get(IntegerType::get(&context, 1)));
        ScopedDiagnosticHandler quiet(&context,
                                      [](Diagnostic &) { return success(); });
        auto checked = protocol::verifySourceExecutionClosure(*module);
        require(
            bool(checked) && namesIdentifier(llvm::toString(std::move(checked)),
                                             "execution-source-closure"),
            "malformed selected signature escaped source closure admission");
      });
  cases.run("source closure checks dormant selected SSA types", [&] {
    checkClosure(changed(closureSource,
                         "func.func @entry(%a: !F, %b: !F) -> !F",
                         "func.func @entry(%a: !F, %b: !F) -> i1"),
                 false);
  });
  cases.run("source closure refuses dormant unadmitted mathematics", [&] {
    checkClosure(
        changed(
            closureSource,
            "%v = algebra.field_multiply %a, %b : (!F, !F) -> !F\n    return",
            "%v = func.call @product(%a, %b) : (!F, !F) -> !F\n    return"),
        false);
  });
  cases.run("source admission keys cannot shadow an actual definition", [&] {
    checkClosure(changed(closureSource, "func.func private @product",
                         "func.func private @_mathematical_admission_0"),
                 true);
  });
  cases.run("source closure permits only checked entry assumptions", [&] {
    auto text = changed(
        bounded, "attributes {data.preconditions = [#data.index_bound<4,1,0>",
        "attributes {no_inline, runtime.origin=[\"caller\", []], "
        "data.preconditions = [#data.index_bound<4,1,0>");
    text = changed(text,
                   "    cf.cond_br %condition, ^invoke, ^via\n  ^via:\n    "
                   "cf.br ^invoke\n  ^invoke:\n",
                   "");
    checkClosure(text, true);
    checkClosure(changed(text, "(%scope, %left, %right, %i)",
                         "(%scope, %unrelated, %right, %j)"),
                 false);
    checkClosure(changed(text, "#data.index_bound<4,1,0>, ", ""), false);
    checkClosure(changed(text, ", #data.equal_extent<1,0,2,0>", ""), false);
  });
  cases.run(
      "source closure rejects helper recursion even with an unused result",
      [&] {
        checkClosure(changed(closureSource, "    %call = \"exec.compute\"",
                             "    %unused = func.call @caller(%scope, %a, %b) "
                             "{runtime.site=\"recurse\"} : (!S, !F, !F) -> !O\n"
                             "    %call = \"exec.compute\""),
                     false);
      });
  cases.run("source closure refuses unsupported invocation attributes", [&] {
    checkClosure(changed(closureSource, "callee = @sum, site = \"sum\"",
                         "callee = @sum, site = \"sum\", authority=true"),
                 false);
  });
  cases.run(
      "source closure cannot turn stopped outcomes into successful results",
      [&] {
        checkClosure(
            changed(closureSource,
                    "%failure = \"exec.failed\"(%cause) : (!exec.stop) -> !O",
                    "%failure = \"exec.returned\"(%a) : (!F) -> !O"),
            false);
      });
  cases.run("source helper return remains uncharged", [&] {
    checkClosure(changed(closureSource, "\"exec.returned\"(%v) : (!F)",
                         "\"exec.complete\"(%scope, %v) : (!S, !F)"),
                 false);
  });
  cases.run(
      "source closure does not grant executable ports to formal quotients",
      [&] {
        checkClosure(R"mlir(
!S = !runtime.scope
!Q = !poly.quotient<12289, 8>
!O = !exec.outcome<(!Q)>
module {
  func.func private @identity(%x: !Q) -> !Q { return %x : !Q }
  func.func @caller(%scope: !S, %x: !Q) -> !O attributes {no_inline, runtime.origin=["caller", []]} {
    %call = "exec.compute"(%scope, %x) {callee=@identity, site="identity"} : (!S, !Q) -> !O
    "exec.dispatch"(%call)[^done, ^failed] : (!O) -> ()
  ^done(%value: !Q):
    %returned = "exec.returned"(%value) : (!Q) -> !O
    return %returned : !O
  ^failed(%stop: !exec.stop):
    %failure = "exec.failed"(%stop) : (!exec.stop) -> !O
    return %failure : !O
  }
})mlir",
                     false);
      });
  for (bool duplicate : {false, true})
    cases.run(
        duplicate ? "source closure refuses duplicated logical affine return"
                  : "source closure preserves a single logical affine return",
        [&] {
          std::string text = R"mlir(
!S = !runtime.scope
!C = !runtime.capability<"resource_unit:Guard">
!O = !exec.outcome<(!C)>
module {
  func.func @caller(%scope: !S, %value: !C) -> !O attributes {no_inline, runtime.origin=["caller", []]} {
    %returned = "exec.returned"(%value) : (!C) -> !O
    return %returned : !O
  }
})mlir";
          if (duplicate) {
            text =
                changed(text, "!exec.outcome<(!C)>", "!exec.outcome<(!C, !C)>");
            text =
                changed(text, "(%value) : (!C)", "(%value, %value) : (!C, !C)");
          }
          checkClosure(text, !duplicate);
        });
  cases.run("source closure with only mathematics keeps its owning admission",
            [&] {
              checkClosure(R"mlir(module {
      func.func private @identity(%x: i1) -> i1 { return %x : i1 }
    })mlir",
                           true);
            });
  cases.run("source closure rejects a missing subject", [&] {
    auto result = protocol::verifySourceExecutionClosure(nullptr);
    require(bool(result) && namesIdentifier(llvm::toString(std::move(result)),
                                            "execution-source-closure"),
            "missing closure subject accepted");
  });
  return cases.result();
}
