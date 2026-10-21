#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
using namespace llvm;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::take;
namespace {
Expected<CheckedProject> check(StringRef source, const Limits &limits = {}) {
  auto captured = capture({{"m", "module m;" + source.str(), {}}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
void compile(StringRef source) {
  auto original = take(prepareOriginal(take(
      zkc::test::closeProtocolDeployment(take(check(source)), "m::Demo"))));
  for (bool simplify : {false, true})
    take(compileEntry(original, {simplify, false}));
}
} // namespace
int main() {
  zkc::test::Cases cases;
  for (StringRef mode : {"fn", "math fn"})
    cases.run("Boolean precedence and nesting in " + mode, [&] {
      compile(mode.str() +
              R"( f(a:bool,b:bool,c:bool){return !a || b && c == false;}
        protocol Run roles(P)(a:bool@P,b:bool@P,c:bool@P)->(r:bool@P){
          return f(c=c,b=b,a=a);
        }run Demo(inputs: Run::Inputs) { return Run::run(inputs); }
      )");
    });
  cases.run("common protocol mathematics and relation formulas", [] {
    compile(R"(
      relation R(statement x:bool,witness w:bool){return x && !w;}
      protocol Run roles(P)(a:bool@P,b:bool@P)->(r:bool@P){return a || b && !a;}
      run Demo(inputs: Run::Inputs) { return Run::run(inputs); }
    )");
    refuses(check("protocol Run "
                  "roles(P,V)(a:bool@P,b:bool@V)->(r:bool@P){return a&&b;}"),
            "source.roles");
    refuses(
        check(
            "protocol Run roles(P,V)(b:bool@V)->(r:bool@P){return false&&b;}"),
        "source.roles");
  });
  for (StringRef expression :
       {"a && {stop \"reject\";}", "a || {stop \"abort\";}",
        "a && {let x=!a;x || a}", "a || (a && {require a;true})"})
    cases.run("local conditional operands: " + expression, [&] {
      compile("fn f(a:bool){return " + expression.str() +
              ";}"
              "protocol Run roles(P)(a:bool@P)->(r:bool@P){return f(a);}run "
              "Demo(inputs: Run::Inputs) { return Run::run(inputs); }");
    });
  cases.run("operand inference shares the enclosing expression", [] {
    take(check(R"(
      fn id<T:Type>(x:T)->T{return x;}
      fn f(a:bool,b:bool){return id(a && {let c=b;c});}
    )"));
    refuses(check("fn f(a:bool){return a&&{let x=0;true};}"),
            "source.inference");
  });
  for (const auto &test : std::vector<std::pair<StringRef, StringRef>>{
           {"!1", "source.type"},
           {"true && 1", "source.type"},
           {"false || ()", "source.type"},
           {"false && missing", "source.name"},
           {"true==false==true", "source.syntax"},
           {"true!=false", "source.syntax"}})
    cases.run("invalid Boolean operand: " + test.first, [&] {
      refuses(check("fn f(){return " + test.first.str() + ";}"), test.second);
    });
  for (StringRef expression :
       {"false && local(x)", "local(x) || true",
        "false && {let unused=local(x);true}", "false && {require x;true}",
        "false && {let mut y=x;y=true;y}"})
    cases.run("protocol formula rejects ordered work: " + expression, [&] {
      refuses(check("fn local(x:bool)->bool effects(){return x;}"
                    "protocol Run roles(P)(x:bool@P)->(r:bool@P){return " +
                    expression.str() + ";}"),
              "source.mode");
    });
  cases.run("protocol formula rejects hidden randomness", [] {
    refuses(check(R"(
      domain F=field("bls12-381.fr");
      math fn ignore(x:F){return true;}
      protocol Run roles(P)(coins:Random<F>@P)->(r:bool@P){
        return false && ignore(coins.draw());
      }
    )"),
            "source.mode");
  });
  cases.run("conditional consumption keeps existing affine joins", [] {
    take(check(R"(
      #[affine] struct Ticket{}
      fn use_ticket(x:Ticket){consume x;return true;}
      fn f(go:bool,x:Ticket){return go&&use_ticket(x);}
    )"));
    refuses(check(R"(
      #[linear] struct Ticket{}
      fn use_ticket(x:Ticket){consume x;return true;}
      fn f(go:bool,x:Ticket){return go&&use_ticket(x);}
    )"),
            "source.drop");
  });
  cases.run("Boolean expansion is bounded", [] {
    std::string expression = "true";
    for (unsigned i = 0; i < 100; ++i)
      expression += " && true";
    refuses(check("fn f(){return " + expression + ";}"), "source.limit");
    refuses(check("fn f(){return " + std::string(1000, '!') + "true;}"),
            "source.limit");
    expression = "true";
    for (unsigned i = 0; i < 100; ++i)
      expression = "true && (" + expression + ")";
    refuses(check("fn f(){return " + expression + ";}"), "source.limit");
  });
  cases.run("protocol operands reject control and primitive calls", [] {
    for (StringRef operand : {"{stop \"abort\";}", "{let r=send P->P(x);r}",
                              "{for _ in 0..n roles(P) max 2 {}true}",
                              "{consume x;true}", "index<0>()==n"})
      refuses(check("protocol Run roles(P)(x:bool@P,n:index@P)->(r:bool@P){"
                    "return false&&" +
                    operand.str() + ";}"),
              "source.mode");
    // Negation has no skipped operand, so an ordered call remains ordered.
    compile("fn f(x:bool){require x;return x;}"
            "protocol Run roles(P)(x:bool@P)->(r:bool@P){return !f(x);}run "
            "Demo(inputs: Run::Inputs) { return Run::run(inputs); }");
    refuses(check("interface Bad{math fn f(x:bool)->bool effects(stop);}"),
            "source.effect");
  });
  return cases.result();
}
