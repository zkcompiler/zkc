#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Dialect/Registry.h"
using namespace llvm;
using namespace zkc::language;
using zkc::test::require;
namespace {
template <class T> T take(Expected<T> value) {
  if (!value) {
    errs() << toString(value.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*value);
}
Expected<CheckedProject> check(StringRef body) {
  return analyze(take(capture({{"sample", ("module sample;" + body).str(),
                                "boolean.zkc"}})))
      .checkedProject();
}
} // namespace
int main() {
  zkc::test::Cases cases;
  const auto program = R"(
    math fn formula(a:bool,b:bool)->bool{
      return intrinsic("bool.and",intrinsic("bool.or",a,b),
                       intrinsic("bool.xor",a,b));
    }
    protocol Run roles(P,V)(a:bool@(P,V),b:bool@(P,V))->(r:bool@(P,V)){
      return(r=formula(a,b));
    }entry Demo=Run;
  )";
  auto original = take(
      prepareOriginal(take(closeEntry(take(check(program)), "sample::Demo"))));
  cases.run("shared mathematical Boolean formulas", [&] {
    for (bool simplify : {false, true})
      take(compileEntry(original, {simplify, false}));
  });
  cases.run("same-type Boolean identity mutation", [&] {
    mlir::DialectRegistry registry;
    zkc::registerDialects(registry);
    mlir::MLIRContext context(registry);
    auto module =
        mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
    require(bool(module), "cannot parse original");
    mlir::Operation *found = nullptr;
    module->walk([&](mlir::Operation *op) {
      if (op->getName().getStringRef() == "arith.andi")
        found = op;
    });
    require(found, "missing Boolean conjunction");
    mlir::OpBuilder builder(found);
    mlir::OperationState state(found->getLoc(), "arith.ori");
    state.addOperands(found->getOperands());
    state.addTypes(found->getResultTypes());
    auto *replacement = builder.create(state);
    found->replaceAllUsesWith(replacement);
    found->erase();
    require(succeeded(mlir::verify(*module)), "mutation must be valid IR");
    auto result = compareOriginal(original.entry(), *module);
    require(!result, "different Boolean identity accepted");
    auto message = toString(result.takeError());
    require(StringRef(message).contains("source.correspondence"), message);
  });
  for (StringRef expression :
       {"intrinsic<1>(\"bool.and\",a,b)", "intrinsic(\"bool.and\",a,b;\"0\")",
        "intrinsic(\"bool.or\",a)", "intrinsic(\"bool.xor\",a,b,a)"})
    cases.run("Boolean hook rejects malformed signature", [&] {
      auto result = check(
          ("math fn f(a:bool,b:bool)->bool{return " + expression + ";}").str());
      require(!result, "invalid hook accepted");
      require(
          StringRef(toString(result.takeError())).contains("source.intrinsic"),
          "wrong malformed hook diagnostic");
    });
  cases.run("Boolean hook rejects non-Boolean operands", [&] {
    auto result = check(R"(
      domain F=field("bls12-381.fr");
      math fn bad(x:F)->bool{return intrinsic("bool.and",x,true);}
    )");
    require(!result, "field operand admitted");
    require(StringRef(toString(result.takeError())).contains("source.type"),
            "wrong operand diagnostic");
  });
  for (StringRef expression : {"intrinsic(\"bool.and\",a,b)", "a==b"})
    for (bool wrapped : {false, true})
      cases.run("unused mathematics retains participant requirements", [&] {
        auto helper =
            ("math fn keep(a:bool,b:bool)->bool{let unused=" + expression +
             ";return a;}")
                .str();
        if (wrapped)
          helper += "math fn relay(a:bool,b:bool)->bool{return keep(a,b);}";
        auto callee = wrapped ? "relay" : "keep";
        auto protocol = [&](StringRef roles) {
          return helper + "protocol Run roles(P,V)(a:bool@P,b:bool@" +
                 roles.str() + ")->(r:bool@P){return(r=" + callee +
                 "(a,b));}entry Demo=Run;";
        };
        take(prepareOriginal(
            take(closeEntry(take(check(protocol("(P,V)"))), "sample::Demo"))));
        auto refused = check(protocol("V"));
        require(!refused, "unavailable helper intermediate admitted");
        require(
            StringRef(toString(refused.takeError())).contains("source.roles"),
            "participant requirement must fail during source analysis");
      });
  cases.run("Boolean hook requires math mode", [&] {
    auto result = check(
        "fn bad(a:bool,b:bool)->bool{return intrinsic(\"bool.and\",a,b);}");
    require(!result, "direct local intrinsic admitted");
    require(StringRef(toString(result.takeError())).contains("source.mode"),
            "wrong mode diagnostic");
  });
  return cases.result();
}
