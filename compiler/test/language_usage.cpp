#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
const std::string prelude = R"(module m;
struct Claim:Share {}
fn make()->Claim {return Claim{};}
fn discharge(x:Claim)->(){consume x;return ();}
fn pair()->(Claim,Claim){return (make(),make());}
)";
Expected<CheckedProject> check(StringRef text) {
  auto captured = capture({{"m", prelude + text.str(), "usage.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
void native(StringRef text) {
  auto entry = take(closeEntry(take(check(text)), "m::Demo"));
  auto original = take(prepareOriginal(entry));
  for (bool simplify : {false, true})
    take(compileEntry(original, {simplify, false}));
}
} // namespace
int main() {
  Cases cases;
  cases.run("early completion cannot skip a live normal-exit obligation", [] {
    refuses(check(R"(
protocol Run roles(P)(go:bool@P)->(accepted:bool@P) completes {
 let claim@P=make();
 let _=finish_if @P(go)(accepted=true);
 let done@P=discharge(claim);return true;
})"),
            "source.drop");
  });
  cases.run("discharged values permit early completion", [] {
    native(R"(
protocol Run roles(P)(go:bool@P)->(accepted:bool@P) completes {
 let claim@P=make();let done@P=discharge(claim);
 let accepted=finish_if @P(go)(accepted=true);return accepted;
}run Demo=Run;)");
  });
  cases.run("nested completion checks obligations outside both loops", [] {
    refuses(check(R"(
protocol Run roles(P)(go:bool@P,n:index@P)->(accepted:bool@P) completes {
 let claim@P=make();
 for _ in 0..n roles(P) max 4 {
  for _ in 0..n roles(P) max 4 {let _=finish_if @P(go)(accepted=true);}
 }
 let done@P=discharge(claim);return true;
})"),
            "source.drop");
  });
  cases.run("completion retains remaining product field obligations", [] {
    refuses(check(R"(
protocol Run roles(P)(go:bool@P)->(accepted:bool@P) completes {
 let claims@P=pair();let done@P=discharge(claims.0);
 let _=finish_if @P(go)(accepted=true);
 let remaining@P=discharge(claims.1);return true;
})"),
            "source.drop");
  });
  cases.run("completion checks only the completing participant", [] {
    native(R"(
protocol Run roles(P,Q)(go:bool@P)->(accepted:bool@P) completes {
 let claim@Q=make();let accepted=finish_if @P(go)(accepted=true);
 let done@Q=discharge(claim);return accepted;
}run Demo=Run;)");
  });
  cases.run("returned resource has a required false-edge successor", [] {
    take(check(R"(
protocol Run roles(P)(go:bool@P)->(claim:Claim@P) completes {
 let claim@P=make();let next=finish_if @P(go)(claim=claim);return next;
})"));
    refuses(check(R"(
protocol Run roles(P)(go:bool@P)->(claim:Claim@P) completes {
 let claim@P=make();let next=finish_if @P(go)(claim=claim);
 let other@P=make();return other;
})"),
            "source.drop");
  });
  cases.run("completion result order follows ports and includes ordinary data",
            [] {
              native(R"(
protocol Run<T:Type+Copy+Drop>roles(P)(go:bool@P,x:T@P)->(a:bool@P,b:T@P)completes {
 let(a,b)=finish_if @P(go)(b=x,a=true);return(a,b);
}run Demo=Run<bool>;)");
            });
  cases.run("an abort waives lower-use obligations but not repeated uses", [] {
    take(check("fn stop_with(claim:Claim)->(){stop \"reject\";}"));
    refuses(check("fn repeat(claim:Claim)->(){consume claim;consume claim;"
                  "stop \"reject\";}"),
            "source.move");
  });
  return cases.result();
}
