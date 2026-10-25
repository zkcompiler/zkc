#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/Execution.h"
#include "llvm/Support/MemoryBuffer.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
std::string read(StringRef name) {
  auto file = llvm::MemoryBuffer::getFile(
      (Twine(ZKC_FIXTURES) + "/runtime/" + name).str());
  require(bool(file), "cannot read runtime scope fixture");
  return (*file)->getBuffer().str();
}
std::string change(std::string source, StringRef from, StringRef to) {
  auto at = source.find(from.str());
  require(at != std::string::npos, "mutation target absent");
  source.replace(at, from.size(), to.str());
  return source;
}
} // namespace
int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  std::vector<std::string> codes;
  ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
    for (auto &refusal : diagnostics::refusals(diagnostic))
      codes.push_back(refusal.code);
    return success();
  });
  auto scope = read("scopes.mlir"), loop = read("scope-loop.mlir");
  auto check = [&](StringRef name, const std::string &source, StringRef entry,
                   bool expected) {
    cases.run(name, [&] {
      auto module = parseSourceString<ModuleOp>(source, &context);
      require(module && succeeded(verify(*module)),
              "ownership fixture must remain structurally valid");
      auto function = module->lookupSymbol<func::FuncOp>(entry);
      require(bool(function), "missing scope fixture entry");
      codes.clear();
      require(succeeded(runtime::verifyScopeOwnership(function)) == expected,
              "unexpected ownership result");
      if (!expected)
        require(llvm::is_contained(codes, "execution-ownership"),
                "ownership refusal lost its diagnostic identifier");
    });
  };
  check("one scope exit and parent handoff", scope, "work", true);
  check("borrowed body scope is not consumed", scope, "body", true);
  check("conditional carry and zero-trip borrowing", loop, "loop", true);
  check("conditional scope shape",
        change(scope, "kind=\"function\", site=\"helper\", callee=@body",
               "kind=\"conditional\", site=\"helper\", selection=\"then\""),
        "work", true);
  check("variant scope shape",
        change(scope, "kind=\"function\", site=\"helper\", callee=@body",
               "kind=\"match\", site=\"helper\", selection=\"present\""),
        "work", true);
  auto reject = [&](StringRef name, const std::string &source, StringRef entry,
                    StringRef from, StringRef to) {
    check(name, change(source, from, to), entry, false);
  };
  reject("borrowed parent cannot be closed", scope, "work",
         "\"runtime.exit_scope\"(%child, %result)",
         "\"runtime.exit_scope\"(%parent, %result)");
  reject(
      "held return cannot be abandoned", scope, "work",
      "%output = \"runtime.accept_transfer\"(%parent, %held) : (!S, !T) -> !R",
      "%output = \"exec.returned\"(%value) : (i1) -> !R");
  reject("held return cannot be accepted twice", scope, "work",
         "func.return %output : !R",
         "%duplicate = \"runtime.accept_transfer\"(%parent, %held) : (!S, !T) "
         "-> !R\n"
         "    func.return %output : !R");
  reject("scope cannot be manufactured by a cast", scope, "work",
         "%result = func.call @body(%child, %value)",
         "%forged = builtin.unrealized_conversion_cast %parent : !S to !S\n"
         "    %result = func.call @body(%child, %value)");
  reject("nested regions require a separate ownership contract", scope, "work",
         "%result = func.call @body(%child, %value)",
         "scf.if %value { scf.yield }\n"
         "    %result = func.call @body(%child, %value)");
  reject("unreachable blocks cannot hide unchecked ownership", scope, "work",
         "func.return %stopped : !R\n  }",
         "func.return %stopped : !R\n"
         "  ^unreachable(%abandoned: !T):\n"
         "    %other = \"exec.returned\"(%value) : (i1) -> !R\n"
         "    func.return %other : !R\n  }");
  reject(
      "ordinary calls cannot receive transferred ownership",
      change(scope, "module {", "module {\n func.func private @sink(!T) -> !R"),
      "work", "%output = \"runtime.accept_transfer\"",
      "%escaped = func.call @sink(%held) : (!T) -> !R\n"
      "    %output = \"runtime.accept_transfer\"");
  reject("old carry released on entry failure", loop, "loop",
         "^release_failure(%failure: !exec.stop):\n"
         "    \"runtime.release_transfer\"(%previous) : (!T) -> ()",
         "^release_failure(%failure: !exec.stop):");
  reject("old carry released only once", loop, "loop",
         "\"runtime.release_transfer\"(%previous) : (!T) -> ()",
         "\"runtime.release_transfer\"(%previous) : (!T) -> ()\n"
         "    \"runtime.release_transfer\"(%previous) : (!T) -> ()");
  reject("initial carry cannot be lost at a join", loop, "loop",
         "cf.cond_br %inside, ^enter, ^finish(%previous : !T)",
         "cf.cond_br %inside, ^enter, ^finish(%initial : !T)");
  reject("new carry cannot be replaced by consumed old carry", loop, "loop",
         "cf.br ^header(%next, %advanced : i64, !T)",
         "cf.br ^header(%next, %previous : i64, !T)");
  reject("transfer cannot be read after publication", loop, "loop",
         "func.return %accepted : !R",
         "%stale = \"runtime.transfer_values\"(%final) : (!T) -> !F\n"
         "    func.return %accepted : !R");
  cases.run("ownership rechecks mutation after success", [&] {
    auto module = parseSourceString<ModuleOp>(scope, &context);
    require(bool(module), "scope fixture did not parse");
    auto function = module->lookupSymbol<func::FuncOp>("work");
    require(succeeded(runtime::verifyScopeOwnership(function)),
            "initial ownership refused");
    function.walk([&](runtime::ExitScopeOp exit) {
      exit.getScopeMutable().assign(function.getArgument(0));
    });
    require(succeeded(verify(*module)), "mutation lost structural validity");
    require(failed(runtime::verifyScopeOwnership(function)),
            "stale ownership result reused");
  });
  auto shape = [&](StringRef name, StringRef from, StringRef to) {
    cases.run(name, [&] {
      codes.clear();
      auto module =
          parseSourceString<ModuleOp>(change(scope, from, to), &context);
      require(!module, "malformed runtime boundary accepted");
      require(llvm::is_contained(codes, "execution-formation"),
              "scope refusal lost its diagnostic identifier");
    });
  };
  shape("unknown scope kind", "kind=\"function\"", "kind=\"unknown\"");
  shape("function entry requires callee", ", callee=@body", "");
  shape("scope occurrence cannot be empty", "site=\"helper\"", "site=\"\"");
  shape("iteration entry requires coordinate",
        "kind=\"function\", site=\"helper\", callee=@body",
        "kind=\"iteration\", site=\"helper\"");
  shape("conditional entry requires selected branch",
        "kind=\"function\", site=\"helper\", callee=@body",
        "kind=\"conditional\", site=\"helper\", selection=\"neither\"");
  shape("match entry requires alternative",
        "kind=\"function\", site=\"helper\", callee=@body",
        "kind=\"match\", site=\"helper\", selection=\"\"");
  auto malformed = [&](StringRef name, StringRef operation) {
    cases.run(name, [&] {
      codes.clear();
      std::string source = R"mlir(module {
        func.func @bad(%parent: !runtime.scope, %b: i1,
            %t: !runtime.transfer<(i1)>, %empty: !runtime.transfer<>,
            %nonbool: !runtime.transfer<(!algebra.field<"koala-bear">)>,
            %out: !exec.outcome<(i1)>) {
      )mlir";
      source += operation.str() + "\n func.return\n }\n }";
      require(!parseSourceString<ModuleOp>(source, &context),
              "malformed transfer boundary accepted");
      require(llvm::is_contained(codes, "execution-formation"),
              "transfer refusal lost its diagnostic identifier");
    });
  };
  malformed("exit must hold exactly the body's values",
            "%r = \"runtime.exit_scope\"(%parent, %out) : "
            "(!runtime.scope, !exec.outcome<(i1)>) -> "
            "!exec.outcome<(!runtime.transfer<>)>");
  malformed("initial transfer must match borrowed values",
            "%r = \"runtime.borrow_transfer\"(%parent, %b) : "
            "(!runtime.scope, i1) -> !runtime.transfer<>");
  malformed("peek must preserve payload types",
            "%r = \"runtime.transfer_values\"(%t) : (!runtime.transfer<(i1)>) "
            "-> ui64");
  malformed(
      "accept must preserve payload types",
      "%r = \"runtime.accept_transfer\"(%parent, %t) : "
      "(!runtime.scope, !runtime.transfer<(i1)>) -> !exec.outcome<(ui64)>");
  malformed(
      "condition needs a leading value",
      "%r = \"runtime.take_condition\"(%empty) : "
      "(!runtime.transfer<>) -> !exec.outcome<(i1, !runtime.transfer<>)>");
  malformed("condition needs a Boolean",
            "%r = \"runtime.take_condition\"(%nonbool) : "
            "(!runtime.transfer<(!algebra.field<\"koala-bear\">)>) -> "
            "!exec.outcome<(i1, !runtime.transfer<>)>");
  malformed("condition exposes an ordinary i1 decision",
            "%r = \"runtime.take_condition\"(%t) : "
            "(!runtime.transfer<(i1)>) -> !exec.outcome<(ui64, "
            "!runtime.transfer<>)>");
  malformed("condition removes only its leading Boolean",
            "%r = \"runtime.take_condition\"(%t) : "
            "(!runtime.transfer<(i1)>) -> !exec.outcome<(i1, "
            "!runtime.transfer<(i1)>)>");
  malformed("control handles cannot be transfer payloads",
            "%r = \"runtime.borrow_transfer\"(%parent) : "
            "(!runtime.scope) -> !runtime.transfer<(!runtime.scope)>");
  malformed("one transfer cannot mix logical and represented stages",
            "%r = \"runtime.borrow_transfer\"(%parent) : "
            "(!runtime.scope) -> !runtime.transfer<(i1, "
            "!runtime.represented<i1, \"native.bool/0\">)>");
  cases.run("scope views are not native carrier descriptors", [&] {
    for (Type type : {Type(runtime::ScopeType::get(&context)),
                      Type(runtime::TransferType::get(&context, {}))})
      for (bool physical : {false, true}) {
        auto encoded = protocol::encodeBoundType(type, physical);
        require(!encoded, "execution ownership acquired a native carrier");
        llvm::consumeError(encoded.takeError());
      }
  });
  cases.run("checked transfer construction refuses a null payload type", [&] {
    codes.clear();
    Type missing;
    auto transfer = runtime::TransferType::getChecked(
        [&] { return emitError(UnknownLoc::get(&context)); }, &context,
        ArrayRef<Type>{missing});
    require(!transfer && llvm::is_contained(codes, "execution-formation"),
            "null transfer payload bypassed checked construction");
  });
  return cases.result();
}
