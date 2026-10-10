#include "zkc/Compiler/Language.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
using namespace llvm;
using namespace zkc::language;
namespace {
template <class T> T must(Expected<T> value) {
  if (!value) {
    errs() << toString(value.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*value);
}
void require(bool condition, StringRef message) {
  if (!condition) {
    errs() << message << '\n';
    std::exit(1);
  }
}
std::string prefix = R"(module m;
domain Fr=field("bls12-381.fr");
struct Ticket:Share {}
struct Required:Copy {}
struct State:Drop { value: Fr }
fn make(x:Fr)->State {return State{value:x};}
fn identity(x:State)->State {return x;}
fn take(x:State)->Fr {let State{value}=x;return value;}
)";
CheckedProject check(StringRef source) {
  auto captured = must(capture({{"m", prefix + source.str(), "lexical.zkc"}}));
  auto project = analyze(captured).checkedProject();
  if (!project) {
    errs() << source << '\n';
    errs() << toString(project.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*project);
}
void refuses(StringRef source, StringRef code) {
  auto captured = must(capture({{"m", prefix + source.str(), "lexical.zkc"}}));
  auto project = analyze(captured).checkedProject();
  if (project) {
    errs() << "unexpected acceptance: " << source << '\n';
    std::exit(1);
  }
  auto diagnostic = toString(project.takeError());
  if (!StringRef(diagnostic).contains(code)) {
    errs() << "expected " << code << ", got " << diagnostic << "\n"
           << source << '\n';
    std::exit(1);
  }
}
CheckedOriginal original(StringRef source) {
  return must(prepareOriginal(must(closeEntry(check(source), "m::Demo"))));
}
void native(StringRef source) {
  auto checked = original(source);
  for (bool simplify : {false, true})
    must(compileEntry(checked, {simplify, false}));
}
void refusesCustody(StringRef source) {
  auto prepared = prepareOriginal(must(closeEntry(check(source), "m::Demo")));
  std::string diagnostic;
  if (!prepared)
    diagnostic = toString(prepared.takeError());
  else {
    auto compiled = compileEntry(*prepared);
    require(!compiled, "replacement resource passed a protocol backedge");
    diagnostic = toString(compiled.takeError());
  }
  require(StringRef(diagnostic).contains("exact carried resource root"),
          diagnostic);
}
void reviewRegressions() {
  refuses("enum Empty{} fn f(e:Empty)->(){match e{} return ();}",
          "source.type");
  refuses("enum One{Only()} fn f(e:One)->(){match e{} return ();}",
          "source.match");
  for (StringRef action : {"require", "consume", "drop"})
    refuses(("fn f()->(){" + action + " {stop \"reject\";};}").str(),
            "source.unreachable");

  for (StringRef source :
       {"fn f(t:Ticket,go:bool)->(){let mut s=t;consume s;if "
        "go{s=Ticket{};consume s;s=Ticket{};}else{s=Ticket{};}consume s;return "
        "();}",
        "fn f(t:Ticket,go:bool,a:bool)->(){let mut s=t;consume s;if go{if "
        "a{s=Ticket{};}else{s=Ticket{};}consume "
        "s;s=Ticket{};}else{s=Ticket{};}consume s;return ();}",
        "fn pair(a:Fr,s:State)->Fr{return a+take(s);}fn "
        "f(x:Fr,go:bool)->Fr{let mut s=make(x);if go{consume s;}else{consume "
        "s;}return pair({s=make(x);x},s);}",
        "fn f(x:Fr,go:bool)->Fr{let mut s=make(x);if go{consume "
        "s;}else{consume s;}return {s=make(x);x}+take(s);}",
        "fn f(k:Required,go:bool)->(){if go{consume k;}consume k;return ();}",
        "fn f(k:Required,go:bool)->(){if go{consume k;}else{consume k;}return "
        "();}",
        "fn f(k:(Required,Required),go:bool)->(){if go{consume k.0;consume "
        "k.1;}else{consume k.0;}consume k.1;return ();}",
        "fn f(k:(Required,Required),go:bool)->(){if go{consume k.0;consume "
        "k.1;}else{let(a,b)=k;consume a;consume b;}return ();}",
        "fn f(x:Fr,go:bool,a:bool)->Fr{let y=if go{if a{stop "
        "\"reject\";}else{stop \"abort\";}}else{x};return y;}",
        "fn f(x:Fr,go:bool,a:bool)->Fr{let y=if go{x}else{if a{stop "
        "\"reject\";}else{stop \"abort\";}};return y;}",
        "fn f(go:bool)->Fr{{if go{stop \"reject\";}else{stop \"abort\";}};}",
        "fn f(go:bool)->Fr{if go{stop \"reject\";}else{stop \"abort\";}}"})
    check(source);
  for (auto [source, code] :
       {std::pair{"fn f(go:bool)->Fr{if go{stop \"reject\";}else{stop "
                  "\"abort\";};let y:Fr=true;return missing(y);}",
                  "source.unreachable"},
        {"fn f()->Fr{{stop \"reject\";}return true;}", "source.unreachable"},
        {"fn f()->Fr{return {stop \"reject\";}+1;}", "source.unreachable"},
        {"fn g(x:Fr,y:Fr)->Fr{return x+y;}fn f()->Fr{return g({stop "
         "\"reject\";},missing());}",
         "source.name"},
        {"fn g(x:Fr,y:Fr)->Fr{return x+y;}fn f()->Fr{return g({stop "
         "\"reject\";},1);}",
         "source.unreachable"},
        {"fn f()->Fr{return if {stop \"reject\";}{1}else{2};}",
         "source.unreachable"},
        {"fn f()->(Fr,Fr){return ({stop \"reject\";},1);}",
         "source.unreachable"},
        {"fn f()->(){let y:Fr={stop \"reject\";true};}", "source.syntax"},
        {"fn f(t:Ticket,go:bool)->(){let mut s=t;consume s;if go{consume "
         "s;s=Ticket{};}else{s=Ticket{};}consume s;return ();}",
         "source.move"},
        {"fn f(k:Required,go:bool)->(){if go{consume k;}return ();}",
         "source.drop"},
        {"fn f(k:Required,go:bool)->(){if go{let alias=k;}consume k;return "
         "();}",
         "source.drop"},
        {"fn f(k:(Required,Required),go:bool)->(){if go{consume "
         "k.0;}else{consume k.1;}consume k.0;return ();}",
         "source.drop"},
        {"fn f(x:Fr,go:bool)->Fr{let y=if go{x}else{true};return y;}",
         "source.type"},
        {"fn f()->(){}", "source.return"},
        {"protocol R roles(P)()->(){}", "source.return"}})
    refuses(source, code);
}

void lexicalBindings() {
  for (StringRef source :
       {"fn f(x:Fr,go:bool)->Fr{return if go capture(x){yield x;}else{yield "
        "x;};}",
        "fn f(n:index)->(){for i in 0..n carry() capture(){}return();}",
        "protocol R roles(P)(x:Fr@P)->(){local P let y=make(x);return();}",
        "protocol R roles(P)()->(){let ()=apply R();return();}"})
    refuses(source, "source.syntax");
  refuses("protocol R roles(P)(coins:Random<Fr>@P)->(){using "
          "alias=coins;return();}",
          "source.syntax");
  check("fn f(x:Fr,go:bool)->Fr{let(a,b)=({let y=x+x;y},if "
        "go{x}else{x+x});return a+b;}");
  check("fn f(x:Ticket)->(){let mut state=x;let "
        "(old,unit)=(state,{state=Ticket{};()});consume old;consume "
        "state;return unit;}");
  for (StringRef source :
       {"fn f(x:Fr)->Fr{let x=x+1; let x=x+2; return x;}",
        "fn f(x:Fr)->Fr{let y={let x=x+1; x}; return x+y;}",
        "fn f(x:Fr)->Fr{let mut y=x; y=y+x; return y;}",
        "math fn f(x:Fr)->Fr{let mut y=x; y=y+x; return y;}",
        "fn f(x:Fr)->Fr{let (a,(b,_))=(x,(x,true));return a+b;}",
        "struct Point{pub x:Fr,pub y:Fr} fn f(x:Fr)->Fr{let p=Point{x,y:x};let "
        "Point{x,y:ordinate}=p;return x+ordinate;}",
        "fn f(x:Fr)->Fr{let mut s=make(x);let old=s;s=make(x);consume "
        "old;return take(s);}",
        "fn f(x:Ticket)->(){let y=x;consume y;return ();}"})
    check(source);
  check("fn f(k:Required)->(){let mut state=k;consume "
        "state;state=Required{};consume state;return ();}");
  check("fn f(p:(Fr,Ticket),go:bool)->(){if go{consume p.1;let "
        "copy=p.0;}else{let(a,b)=p;consume b;}return ();}");
  for (auto [source, code] :
       {std::pair{"fn f(x:Fr)->Fr{x=x+1;return x;}", "source.assignment"},
        {"fn f(x:Fr)->Fr{let mut x=x;{let x=x+1;}return x;}", "source.shadow"},
        {"fn f(x:Fr)->Fr{let mut y=x; y=true;return y;}", "source.type"},
        {"fn f()->(){let mut x=0;return ();}", "source.inference"},
        {"fn f()->(){let t=Ticket{};let alias=t;return ();}", "source.drop"},
        {"fn f()->(){let t=Ticket{};let _=t;return ();}", "source.drop"},
        {"fn f()->(){Ticket{};return ();}", "source.drop"},
        {"fn f()->(){let mut t=Ticket{};t=Ticket{};consume t;return ();}",
         "source.drop"},
        {"fn f(x:Fr)->Fr{let y={let z=x;z};return z;}", "source.name"},
        {"fn f()->(){stop \"reject\";let x=true;return ();}", "source.syntax"}})
    refuses(source, code);
}
void control() {
  for (StringRef source :
       {"fn f(x:Fr,go:bool)->Fr{let mut y=x;if go{y=y+x;}return y;}",
        "fn f(x:Fr,go:bool)->Fr{let y=if go{x}else{x+x};return y;}",
        "fn f(x:Fr,n:index)->Fr{let mut y=x;for _ in 0..n{y=y+x;}return y;}",
        "fn f(x:Fr,n:index)->Fr{let mut y=x;for _ in 0..n{for _ in "
        "0..n{y=y+x;}}return y;}",
        "fn f(x:State,go:bool)->State{let mut s=x;if go{s=identity(s);}return "
        "s;}",
        "fn f(x:Fr,go:bool)->State{let mut s=make(x);consume s;if "
        "go{s=make(x);}else{s=make(x);}return s;}",
        "fn f(t:Ticket,go:bool)->(){let moved=if go{t}else{stop "
        "\"reject\";};consume moved;return ();}",
        "fn f(go:bool)->(){let x:Fr=if go{stop \"reject\";}else{stop "
        "\"abort\";};}",
        "fn f(x:Fr,n:index)->Fr{let mut s=make(x);for _ in 0..n{consume "
        "s;s=make(x);}return take(s);}",
        "fn f(a:Ticket,b:Ticket,go:bool)->(){let mut p=(a,b);consume p.0;if "
        "go{consume p.1;}else{consume p.1;}return ();}",
        "fn f(a:Ticket,b:Ticket,go:bool)->(){let mut p=(a,b);consume p.0;if "
        "go{consume p.1;p=(Ticket{},Ticket{});}else{consume "
        "p.1;p=(Ticket{},Ticket{});}consume p.0;consume p.1;return ();}",
        "fn f(a:Ticket,x:Fr,n:index)->Fr{let mut p=(a,x);consume p.0;let mut "
        "sum=x;for _ in 0..n{sum=sum+p.1;}return sum;}",
        "fn f(k:Required,n:index)->(){for _ in 0..n{consume k;}consume "
        "k;return ();}",
        "fn f(x:(Fr,Ticket),n:index)->Fr{let mut y=x.0;for _ in "
        "0..n{y=y+x.0;}consume x.1;return y;}"})
    check(source);
  for (auto [source, code] :
       {std::pair{
            "fn f(t:Ticket,n:index)->(){for _ in 0..n{consume t;}return ();}",
            "source.permission"},
        {"fn f(t:Ticket,go:bool)->(){if go{consume t;}return ();}",
         "source.drop"},
        {"fn f(k:Required,n:index)->(){for _ in 0..n{consume k;}return ();}",
         "source.drop"},
        {"fn f(s:State)->Fr{return s.value;}", "source.private"},
        {"fn f(s:State,go:bool)->Fr{return if go{s.value}else{s.value};}",
         "source.private"},
        {"fn f(x:Fr,n:index)->(){let mut s=make(x);consume s;for _ in "
         "0..n{s=make(x);}consume s;return ();}",
         "source.move"},
        {"fn f(x:State,go:bool)->State{let mut s=x;if go{consume s;}return s;}",
         "source.move"},
        {"fn f(go:bool)->(){let x=if go{stop \"reject\";}else{stop "
         "\"abort\";};}",
         "source.inference"},
        {"fn f(x:Fr,go:bool)->(){if go{x}return ();}", "source.type"},
        {"fn f(x:Fr,go:bool)->(){if go{let _=x;}+x;return ();}",
         "source.name"}})
    refuses(source, code);
  refuses("fn f<T:Type>(x:T,n:index)->T{for _ in 0..n{let y=x;}return x;}",
          "source.permission");
  refuses("fn f(t:Ticket)->(){if true{consume t;}return ();}", "source.drop");
  refuses("fn f(t:Ticket,go:bool)->(){let mut s=t;consume s;if "
          "go{s=Ticket{};}return ();}",
          "source.drop");
  refuses("struct Flag{pub value:bool} fn f(x:bool)->bool{return if "
          "(Flag{value:x}){true}else{false};}",
          "source.type");
  refuses("struct Flag{pub value:bool} fn f(x:bool)->bool{return if "
          "Flag{value:x}.value{true}else{false};}",
          "source.syntax");
}
void protocols() {
  auto count = original(R"(
    math fn count(n:index,x:Fr)->index{return n;}
    protocol Run roles(P)(n:index@P, coins:Random<Fr>@P)->(){
      for _ in 0..count(n,coins.draw()) roles(P) max 4{}return();
    }run Demo=Run;
  )");
  bool queried = false, repeated = false;
  for (const auto &operation : count.entry().protocol().body->operations) {
    if (std::holds_alternative<ServiceQuery>(operation.action)) {
      require(!queried && !repeated,
              "count query must occur once before repetition");
      queried = true;
    }
    if (auto *loop = std::get_if<ProtocolRepeat>(&operation.action)) {
      require(queried, "loop preceded its count query");
      repeated = true;
      for (const auto &nested : loop->region->operations)
        require(!std::holds_alternative<ServiceQuery>(nested.action),
                "count query moved into repeated region");
    }
  }
  require(queried && repeated, "missing count query or repetition");
  must(compileEntry(count));
  native(R"(
    protocol Run roles(P)(n:index@P,go:bool@P,x:Fr@P)->(a:State@P,b:State@P,data:Fr@P)completes{
      let mut a@P=make(x);let mut b@P=make(x);
      for _ in 0..n roles(P) max 4{
        let (nextA,nextB)=finish_if @P(go)(data=x,b=b,a=a);
        a=nextA;b=nextB;
      }return(a,b,data=x);
    }run Demo=Run;
  )");
  refuses("fn ticket()->Ticket{return Ticket{};} protocol Make "
          "roles(P)()->(r:Ticket@P){let t@P=ticket();return t;} protocol R "
          "roles(P)()->(){Make();return();}",
          "source.drop");
  native(R"(
    fn aborting(t:Ticket,go:bool)->(){if go{stop "reject";}else{stop "abort";}}
    fn work(go:bool)->(){let t=Ticket{};return aborting(t,go);}
    protocol Run roles(P)(go:bool@P)->(){let done@P=work(go);return ();}run Demo=Run;
  )");
  check("fn f(t:Ticket)->Fr{return {stop \"reject\";};}");
  check("fn f(t:Ticket)->(){{stop \"reject\";}}");
  check("fn f(t:Ticket)->(){{stop \"reject\";};}");
  check("fn f(t:Ticket,go:bool)->(){if go{stop \"reject\";}else{stop "
        "\"abort\";};}");
  check("fn f(x:Fr,go:bool)->(){if go{x}else{x+x};return ();}");
  refuses("fn f()->(){let v={stop \"reject\";};return ();}",
          "source.inference");
  native(R"(
    fn work(n:index)->(){let mut ticket=Ticket{};for _ in 0..n{ticket=ticket;}consume ticket;return ();}
    protocol Run roles(P)(n:index@P)->(){let done@P=work(n);return ();}run Demo=Run;
  )");
  native(R"(
    fn step(s:State,go:bool)->State{let mut current=s;if go{current=identity(current);}return current;}
    protocol Run roles(P)(n:index@P,x:Fr@P,go:bool@P)->(r:Fr@P){
      let mut state@P=make(x);
      for _ in 0..n roles(P) max 4{state=step(state,go);}
      let result@P=take(state);return result;
    }run Demo=Run;
  )");
  native(R"(
    fn step(a:State,b:State,go:bool)->(State,State){let mut x=a;let mut y=b;if go{x=identity(x);y=identity(y);}return (x,y);}
    fn first(a:State,b:State,go:bool)->State{let (x,y)=step(a,b,go);consume y;return x;}
    protocol Run roles(P)(n:index@P,x:Fr@P,go:bool@P)->(r:Fr@P){
      let mut state@P=make(x);
      for _ in 0..n roles(P) max 4{let other@P=make(x);state=first(state,other,go);}
      let result@P=take(state);return result;
    }run Demo=Run;
  )");
  native(R"(
    protocol Run roles(P)(n:index@P,go:bool@P,x:Fr@P)->(state:State@P)completes{
      let mut state@P=make(x);for _ in 0..n roles(P) max 4{
        let next=finish_if @P(go)(state=state);state=next;
      }return state;
    }run Demo=Run;
  )");
  native(R"(
    protocol Pair roles(P,V)(p:Fr@P,v:Fr@V)->(p:Fr@P,v:Fr@V){return(p,v);}
    protocol Observe roles(P,V)()->(){return ();}
    protocol Run roles(P,V)(p:Fr@P,v:Fr@V)->(p:Fr@P,v:Fr@V){let(a,b)=Pair(p,v);Observe();return(v=b,p=a);}
    run Demo=Run;
  )");
  auto queries = original(R"(
    protocol Run roles(P,V)(n:index@V, coins:Random<Fr>@V)->(r:Fr@V){
      let alias=coins;let mut total:Fr@V=0;
      for _ in 0..n roles(V) max 4{total=total+alias.draw()+coins.draw();}
      return total;
    }run Demo=Run;
  )");
  require(queries.bytes().count("\"protocol.query\"") == 2,
          "two draws must remain two ordered queries");
  must(compileEntry(queries));
  auto returns = original(R"(
    protocol Run roles(P)(coins:Random<Fr>@P)->(first:Fr@P,second:Fr@P){
      return(second=coins.draw(),first=coins.draw());
    }run Demo=Run;
  )");
  const auto &body = *returns.entry().protocol().body;
  require(body.results[0].index > body.results[1].index,
          "named return expressions must evaluate in written order");
  native(R"(
    protocol Tuple roles(P)(x:Fr@P)->(pair:(Fr,Fr)@P){return(x,x);}
    protocol Run roles(P)(x:Fr@P)->(r:Fr@P){let(a,b)=Tuple(x);return a+b;}run Demo=Run;
  )");
  native(R"(
    protocol Run roles(P,V)(n:index@V,x:Fr@(P,V))->(r:Fr@V){
      let mut shared=x;let mut result=x;
      for _ in 0..n roles(V) max 4 {let copied=shared;}
      return result;
    }run Demo=Run;
  )");
  refusesCustody(R"(
    protocol Run roles(P)(n:index@P,x:Fr@P)->(r:Fr@P){let mut state@P=make(x);
      for _ in 0..n roles(P) max 4{state=make(x);}
      let result@P=take(state);return result;
    }run Demo=Run;
  )");
  refusesCustody(R"(
    protocol Run roles(P)(n:index@P,x:Fr@P)->(r:Fr@P){let mut a@P=make(x);let mut b@P=make(x);
      for _ in 0..n roles(P) max 4{let temp=a;a=b;b=temp;}
      let result@P=take(a);let unused@P=take(b);return result;
    }run Demo=Run;
  )");
  for (auto [source, code] :
       {std::pair{"protocol R roles(P,V)(x:Fr@(P,V),n:index@P)->(){let mut "
                  "s=x;for _ in "
                  "0..n roles(P) max 4{s=s+x;}return ();}",
                  "source.roles"},
        {"protocol R roles(P)(n:index@P)->(){for _ in 1..n roles(P) max "
         "4{}return ();}",
         "source.bound"},
        {"protocol R roles(P)(n:index@P)->(){for _ in 0..n{}return ();}",
         "source.mode"},
        {"protocol R roles(P,W)(n:index@P,x:Fr@W)->(){for _ in 0..n roles(P) "
         "max 4{let y=x;}return ();}",
         "source.roles"},
        {"protocol R roles(P,V)(x:Fr@P)->(){let mut "
         "state:Fr@(P,V)=0;state=x;return ();}",
         "source.roles"},
        {"protocol R roles(P)(x:State@P)->(r:Fr@P){let State{value}=x;return "
         "value;}",
         "source.mode"},
        {"protocol R roles(P)(coins:Random<Fr>@P)->(){let mut "
         "alias=coins;return ();}",
         "source.service"},
        {"protocol R roles(P)(x:State@P,go:bool@P)->(r:State@P)completes{let "
         "mut s=x;s=finish_if @P(go)(r=s);return s;}",
         "source.mode"}})
    refuses(source, code);
}
} // namespace
int main() {
  reviewRegressions();
  lexicalBindings();
  control();
  protocols();
  outs() << "lexical bindings, resource joins, inferred regions and protocol "
            "authoring passed\n";
}
