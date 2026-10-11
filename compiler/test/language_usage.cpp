#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
const std::string prelude = R"(module m;
#[linear] struct Claim {}
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
  auto contract = [&](StringRef text, StringRef name, bool copy, bool drop) {
    auto checked = take(check(text));
    const Declaration *target = nullptr;
    for (const auto &decl : checked.declarations())
      if (decl.name == name)
        target = &decl;
    require(target, "missing declaration");
    require(target->permissionBounds.size() == (drop ? 1u : 0u),
            "unexpected inferred usage requirements");
    if (drop) {
      const auto &bound = target->permissionBounds.front();
      require(bound.inferred && bound.permissions.copy == copy &&
                  bound.permissions.drop,
              "incorrect inferred usage property");
    }
  };
  cases.run("generic identity is unrestricted", [&] {
    contract("fn identity<T:Type>(x:T)->T{return x;}", "identity", false,
             false);
  });
  cases.run("generic duplication and abandonment infer usage", [&] {
    contract("fn duplicate<T:Type>(x:T)->(T,T){return(x,x);}", "duplicate",
             true, true);
    contract("fn ignore<T:Type>(x:T)->(){return ();}", "ignore", false, true);
  });
  cases.run(
      "callee usage propagates without strengthening concrete types", [&] {
        contract(R"(
fn forward<T:Type>(x:T)->(T,T){return duplicate(x);}
fn duplicate<T:Type>(x:T)->(T,T){return(x,x);}
)",
                 "forward", true, true);
        refuses(check(R"(
fn duplicate<T:Type>(x:T)->(T,T){return(x,x);}
fn invalid(x:Claim)->(Claim,Claim){return duplicate(x);}
)"),
                "source.permission");
        refuses(
            check("fn duplicate<T:Type>(x:T)->(T,T) where (){return(x,x);}"),
            "source.move");
      });
  cases.run(
      "exclusive forwards and stopped arms preserve generic resources", [&] {
        contract("fn choose<T:Type>(x:T,b:bool)->T{return if b{x}else{x};}",
                 "choose", false, false);
        contract("fn choose<T:Type>(x:T,b:bool)->T{return if b{x}else{stop "
                 "\"reject\";};}",
                 "choose", false, false);
        contract("fn choose<T:Type>(x:T,y:T,b:bool)->T{return if b{x}else{y};}",
                 "choose", false, true);
        contract(
            "fn stop_twice<T:Type>(x:T)->(){let y=x;let z=x;stop \"reject\";}",
            "stop_twice", true, true);
      });
  cases.run("restoring moved mutable state does not infer Copy", [&] {
    contract(R"(
fn restore<T:Type>(a:T,b:T,go:bool)->(T,T) {
 let mut state=a;let used=state;
 if go {state=b;} else {state=b;}
 return (used,state);
})",
             "restore", false, false);
    contract(R"(
fn identity<T:Type>(x:T)->T{return x;}
fn thread<T:Type>(x:T,b:bool,n:index)->T {
 let mut state=x;
 if b {state=identity(state);} else {}
 for _ in 0..n {state=identity(state);}
 return state;
})",
             "thread", false, false);
  });
  cases.run("stopped captures retain the outer transfer", [&] {
    contract(R"(
fn guard<T:Type>(x:T,bad:bool)->T {
 if bad {let y=x;stop "reject";} else {}
 return x;
})",
             "guard", true, true);
    take(check(R"(
fn guard<T:Type>(x:T,bad:bool)->T where Copy(T) {
 if bad {let y=x;stop "reject";} else {}
 return x;
})"));
    refuses(check(R"(
fn guard<T:Type>(x:T,bad:bool)->T where Drop(T) {
 if bad {let y=x;stop "reject";} else {}
 return x;
})"),
            "source.move");
  });
  cases.run("partial state moves preserve the whole joined successor", [&] {
    contract(R"(
fn tail<T:Type>(p:(T,T),q:(T,T),b:bool)->(T,T) {
 let mut state=p;let first=state.0;
 if b {state=q;} else {}
 return(first,state.1);
})",
             "tail", true, true);
    take(check(R"(
fn tail<T:Type>(p:(T,T),q:(T,T),b:bool)->(T,T) where Copy(T) {
 let mut state=p;let first=state.0;
 if b {state=q;} else {}
 return(first,state.1);
})"));
    refuses(check(R"(
fn tail<T:Type>(p:(T,T),q:(T,T),b:bool)->(T,T) where Drop(T) {
 let mut state=p;let first=state.0;
 if b {state=q;} else {}
 return(first,state.1);
})"),
            "source.move");
  });
  cases.run("repeated invariant use infers Copy", [&] {
    contract("fn repeat<T:Type>(x:T,n:index)->(){for _ in 0..n {let "
             "value=x;}return ();}",
             "repeat", true, true);
  });
  cases.run("associated generic usage stays a callable requirement", [&] {
    contract(R"(
interface Family {type Item;}
fn duplicate<C:Family>(x:C::Item)->(C::Item,C::Item){return(x,x);}
)",
             "duplicate", true, true);
  });
  cases.run("inferred member requirements cannot strengthen an interface", [] {
    refuses(check(R"(
interface Copier<T:Type> {fn duplicate(x:T)->(T,T) effects();}
module Bad<T:Type>:Copier<T> {
 fn duplicate(x:T)->(T,T){return(x,x);}
})"),
            "source.conformance");
    take(check(R"(
interface Copier<T:Type> {fn duplicate(x:T)->(T,T) effects() where Copy(T);}
module Good<T:Type>:Copier<T> {
 fn duplicate(x:T)->(T,T){return(x,x);}
})"));
  });
  cases.run("aggregate requirements retain the precise generic leaf", [] {
    auto checked = take(check(R"(
fn first<T:Type,U:Type>(x:(T,U))->T{return x.0;}
fn duplicate_first<T:Type,U:Type>(x:(T,U))->(T,T,U){return(x.0,x.0,x.1);}
)"));
    for (const auto &decl : checked.declarations()) {
      if (decl.name != "first" && decl.name != "duplicate_first")
        continue;
      require(decl.permissionBounds.size() == 1,
              "nonminimal aggregate requirements");
      const auto &bound = decl.permissionBounds.front();
      const bool duplicate = decl.name == "duplicate_first";
      require(bound.type.domain == decl.parameters[duplicate ? 0 : 1].atom &&
                  bound.permissions.copy == duplicate && bound.permissions.drop,
              "wrong aggregate leaf requirement");
    }
  });
  cases.run("generic mathematical data and zero arrays retain their contracts",
            [&] {
              contract("math fn identity<T:Type>(x:T)->T{return x;}",
                       "identity", true, true);
              contract("fn ignore<T:Type>(x:[T;0])->(){return ();}", "ignore",
                       false, true);
            });
  cases.run("planning keeps lazily completed callback witnesses", [&] {
    contract(R"(
fn caller<T:Type>(x:T)->T{return forward(x,fn(y)=>y);}
fn forward<T:Type>(x:T,f:fn(T)->T)->T{return invoke(x,fn(y)=>f(y));}
fn invoke<T:Type>(x:T,f:fn(T)->T)->T{return f(x);}
)",
             "caller", false, false);
  });
  cases.run("hidden callback captures infer reusable data", [&] {
    contract(R"(
fn caller<T:Type>(x:T)->T{return invoke(fn()=>x);}
fn invoke<T:Type>(f:fn()->T)->T{return f();}
)",
             "caller", true, true);
  });
  cases.run("inferred resource threading lowers under the frozen contract", [] {
    native(R"(
fn identity<T:Type>(x:T)->T{return x;}
fn thread<T:Type>(x:T,b:bool,n:index)->T {
 let mut state=x;
 if b {state=identity(state);} else {}
 for _ in 0..n {state=identity(state);}
 return state;
}
protocol Run roles(P)(b:bool@P,n:index@P)->(accepted:bool@P) {
 let claim@P=make();let next@P=thread(claim,b,n);
 let done@P=discharge(next);return true;
}run Demo=Run;
)");
  });
  cases.run("early generic completion infers its normal-exit obligation", [&] {
    contract(R"(
protocol Finish<T:Type>roles(P)(go:bool@P,x:T@P)->(result:T@P) completes {
 let next=finish_if @P(go)(result=x);return next;
})",
             "Finish", false, false);
    contract(R"(
protocol Finish<T:Type>roles(P)(go:bool@P,x:T@P)->(accepted:bool@P) completes {
 let accepted=finish_if @P(go)(accepted=true);return accepted;
})",
             "Finish", false, true);
  });
  cases.run("signature and installed definitions infer formation requirements",
            [&] {
              contract(R"(
fn length<T:Type>(xs:builtin("sequence",T))->index=primitive("sequence.length");
)",
                       "length", true, true);
              refuses(check(R"(
fn length<T:Type>(xs:builtin("sequence",T))->index where ()=primitive("sequence.length");
)"),
                      "source.sequence");
              contract(R"(
fn fold<I:Type,S:Type>(rows:domain<I>,initial:S,step:fn(S,item:I)->S effects(stop) where item_from(item, rows))->S effects(stop)=finite("local.fold");
)",
                       "fold", true, true);
              contract(R"(
domain fn indices<T:Type>(xs:builtin("sequence",T))->domain<index>=domain("indices");
)",
                       "indices", true, true);
            });
  cases.run("ordinary and sealed data derive reusable usage", [] {
    take(check(R"(
struct Data {pub flag:bool}
#[sealed] struct Snapshot {pub flag:bool}
fn copies(x:Data,s:Snapshot)->(Data,Data){let ignored=s;return(x,x);}
fn copy_implies_drop<T:Type+Copy>(x:T)->(){return ();}
module Box {
 type State:Type=bool;
 fn duplicate(s:State)->(State,State){return(s,s);}
}
)"));
  });
  cases.run("protocol products transfer generic resources structurally", [] {
    take(check(R"(
protocol Pair<T:Type> roles(P)(x:T@P,y:T@P)->(pair:(T,T)@P) {
 return (x,y);
})"));
  });
  cases.run("explicit resource restrictions are structural", [] {
    take(check(
        "#[affine] struct Optional {} fn ignore(x:Optional)->(){return ();}"));
    refuses(check("#[affine] struct Invalid {value:Claim}"),
            "source.permission");
    refuses(check("struct Wrapper {pub value:Claim} "
                  "fn duplicate(x:Wrapper)->(Wrapper,Wrapper){return(x,x);}"),
            "source.move");
    refuses(check("#[linear] struct Required {} "
                  "fn ignore(x:Required)->(){return ();}"),
            "source.drop");
  });
  cases.run(
      "resource attributes reject contradictions and unrelated declarations",
      [] {
        refuses(check("#[affine] #[linear] struct Conflict {}"),
                "source.resource");
        refuses(check("#[sealed] fn invalid()->(){return ();}"),
                "source.resource");
        refuses(check("#[linear] type Conflict:Copy=bool;"), "source.resource");
        refuses(check(R"(
interface Linear {#[linear] type Token;}
fn duplicate<C:Linear>(x:C::Token)->(C::Token,C::Token)
 where Copy(C::Token) {return(x,x);}
)"),
                "source.move");
      });
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
  cases.run("completion cannot interrupt pending operand transfers", [] {
    refuses(check(R"(
fn discharge2(x:Claim,u:())->(){consume x;return ();}
protocol Run roles(P)(go:bool@P)->(accepted:bool@P) completes {
 let claim@P=make();
 let done@P=discharge2(claim,{let _=finish_if @P(go)(accepted=true);()});
 return true;
})"),
            "source.completion");
    refuses(check(R"(
fn discharge2(x:Claim,u:())->(){consume x;return ();}
protocol Run roles(P)(go:bool@P,n:index@P)->(accepted:bool@P) completes {
 let claim@P=make();
 let done@P=discharge2(claim,{
  for _ in 0..n roles(P) max 4 {let _=finish_if @P(go)(accepted=true);}
  ()
 });return true;
})"),
            "source.completion");
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
