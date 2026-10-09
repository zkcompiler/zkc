#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Builtins.h"
#include "zkc/Language/Layout.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <functional>
using namespace llvm;
using namespace zkc::language;
namespace {
void require(bool condition, StringRef message) {
  if (!condition) {
    errs() << message << '\n';
    std::exit(1);
  }
}
template <class T> T must(Expected<T> value) {
  if (!value) {
    errs() << toString(value.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*value);
}
CheckedProject check(StringRef source, const Limits &limits = {}) {
  return must(analyze(must(capture({{"m", source.str(), "types.zkc"}})), limits)
                  .checkedProject());
}
void refuses(StringRef source, StringRef code, const Limits &limits = {}) {
  auto value =
      analyze(must(capture({{"m", source.str(), "types.zkc"}})), limits)
          .checkedProject();
  if (value) {
    errs() << "unexpected acceptance: " << source << '\n';
    std::exit(1);
  }
  auto message = toString(value.takeError());
  if (!StringRef(message).contains(code)) {
    errs() << "expected " << code << ", got " << message << " in " << source
           << '\n';
    std::exit(1);
  }
}
void closureRefuses(StringRef source, StringRef code,
                    const Limits &limits = {}) {
  auto project = check(source, limits);
  auto selected = closeEntry(project, "m::Demo", limits);
  require(!selected, "Entry closure unexpectedly accepted");
  auto message = toString(selected.takeError());
  require(StringRef(message).contains(code), message);
}
CheckedOriginal original(StringRef source) {
  return must(prepareOriginal(must(closeEntry(check(source), "m::Demo"))));
}
mlir::Operation *first(mlir::ModuleOp module, StringRef name) {
  mlir::Operation *found = nullptr;
  module.walk([&](mlir::Operation *op) {
    if (!found && op->getName().getStringRef() == name)
      found = op;
  });
  require(found, "missing mutation target");
  return found;
}
void mutation(const CheckedOriginal &source,
              const std::function<void(mlir::ModuleOp)> &edit) {
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  auto module =
      mlir::parseSourceString<mlir::ModuleOp>(source.bytes(), &context);
  require(bool(module), "cannot parse original");
  edit(*module);
  require(succeeded(mlir::verify(*module)),
          "mutation must remain valid native IR");
  auto comparison = compareOriginal(source.entry(), *module);
  require(!comparison, "mutation escaped correspondence");
  require(StringRef(toString(comparison.takeError()))
              .contains("source.correspondence"),
          "wrong mutation refusal phase");
}
const std::string prefix = "module m;domain Fr=field(\"bls12-381.fr\");\n";
const std::string unit =
    "protocol Run roles(P)()->(){return();}entry Demo=Run;";
void wireAuthority() {
  const std::string relay = R"(
protocol Relay<T:Type+Copy+Drop+Share+Wire> roles(P,V)(x:T@P)->(r:T@V){
  let y=send P->V(x);return(r=y);
}
)";
  for (const auto &type : {"Fr", "bool", "Pair<Fr>", "Choice", "[Fr;2]"}) {
    auto checked = original(prefix + R"(
struct Pair<T:Type>{pub first:T,pub second:T}
enum Choice{Some(Fr),None()}
)" + relay + "entry Demo=Relay<" +
                            type + ">;");
    must(compileEntry(checked));
  }
  for (const auto &definition :
       {"struct Secret {value:Fr}",
        "struct Secret:Copy+Drop+Share {pub value:Fr}",
        "enum Secret:Copy+Drop+Share {Some(Fr)}",
        "struct Hidden{value:Fr}struct Secret{pub value:Hidden}"})
    refuses(prefix + definition + relay + "entry Demo=Relay<Secret>;",
            "source.permission");
  closureRefuses(
      prefix +
          "struct Secret{value:Fr}protocol Run "
          "roles(P)(x:Secret@P)->(r:Secret@P){return(r=x);}entry Demo=Run;",
      "source.ingress");
  refuses(prefix +
              "interface I{type State:Wire;}component C:I{type State:Wire=Fr;}",
          "source.permission");
  auto emitted = original(prefix + R"(
struct Secret{value:Fr}
fn make()->Secret{return Secret{value:1};}
protocol Run roles(P)()->(r:Secret@P){let x @P =make();return(r=x);}
entry Demo=Run;
)");
  auto schema = must(json::parse(emitted.interfaceJson()));
  auto *permissions = schema.getAsObject()
                          ->getArray("protocols")
                          ->front()
                          .getAsObject()
                          ->getArray("outputs")
                          ->front()
                          .getAsObject()
                          ->getObject("schema")
                          ->getArray("permissions");
  require(*permissions == json::Array{"Copy", "Drop", "Share"},
          "private output schema incorrectly advertises Wire");
}
void typing() {
  for (auto &[source, code] : std::vector<std::pair<std::string, std::string>>{
           {"math fn bad<T:Type>(x:T)->T{return x;}", "source.mode"},
           {"struct Bad<T:Type>:Copy {pub value:T}", "source.permission"},
           {"type Recursive=Recursive;", "source.cycle"},
           {"struct Recursive {pub next:Recursive}", "source.cycle"},
           {"enum Bad {A(),A()}", "source.duplicate"},
           {"enum Empty {}", "source.type"},
           {"interface Bad {domain F=field(\"bls12-381.fr\");}",
            "source.syntax"},
           {"interface Bad {entry Demo=Run;}", "source.syntax"},
           {"fn bad(a:[Fr;2])->Fr{return a[2];}", "source.index"},
           {"fn bad(a:[Fr;2],i:index)->Fr{return a[i];}", "source.index"},
           {"math fn bad<F:Field>(x:F)->F{return x+2;}", "source.literal"},
           {"fn bad<N:nat>(x:[Fr;N])->Fr{return x[0];}", "source.bound"},
           {"type Bad=[Fr;18446744073709551615+1];", "source.natural"},
           {"fn bad<N:nat+Copy>()->bool{return true;}", "source.permission"},
           {"fn bad<N:nat>()->bool where Copy(N) {return true;}",
            "source.permission"},
           {"fn bad(x:Fr)->bool !{} {require true;return true;}",
            "source.effect"},
           {"fn bad(x:Fr)->Fr {let y=if true { missing}else{ x};return y;}",
            "source.name"},
           {"enum Choice {A(Fr),B()} fn bad(v:Choice)->Fr {return match v "
            "{A(x)=>{ x}};}",
            "source.match"},
           {"enum Choice {A(Fr),B()} fn bad(v:Choice)->Fr {return match v "
            "{A(x)=>{ x},A(x)=>{ x}};}",
            "source.match"},
           {"struct Pair {pub left:Fr,pub right:Fr} fn bad(x:Fr)->Pair{return "
            "Pair{left:x,left:x};}",
            "source.duplicate"},
           {"fn bad<T:Type+Copy>(x:T)->bool{return true;}", "source.drop"},
           {"struct Token:Drop {} fn bad(t:Token)->(Token,Token){return(t,t);}",
            "source.move"},
           {"struct Token:Copy {} fn bad(t:Token)->bool{return true;}",
            "source.drop"},
           {"struct Token:Copy {} fn bad(t:Token)->(){drop t;return ();}",
            "source.drop"},
           {"struct Token:Share {} fn bad(t:Token,go:bool)->Token{return if go "
            "{ t}else{ Token{}};}",
            "source.drop"},
           {"struct Token:Drop {} fn bad(t:Token,n:index)->(){for _ in 0..n "
            "{consume t;}return ();}",
            "source.permission"},
           {"struct Token:Drop {} struct Pair {pub a:Token,pub b:Token} fn "
            "bad(p:Pair)->Pair{let a=p.a;return p;}",
            "source.move"},
           {"struct Token:Copy {} struct Pair {pub a:Token,pub b:Token} fn "
            "bad(p:Pair)->Token{return p.a;}",
            "source.drop"},
           {"interface I{math fn f(x:bool)->bool;}component C:I{fn "
            "f(x:bool)->bool{return x;}}",
            "source.conformance"},
           {"interface I{fn f(x:bool)->bool !{};}component C:I{fn "
            "f(x:bool)->bool{require x;return x;}}",
            "source.effect"},
           {"interface I{type Scalar:Field;}component C:I{type "
            "Scalar:Field=bool;}",
            "source.type"},
           {"interface I{type State:Copy+Drop;}component C:I{type "
            "State:Drop=bool;}",
            "source.conformance"},
           {"interface I{}interface J{}component C:I{}fn f<T:J>()->bool{return "
            "true;}fn bad()->bool{return f<C>();}",
            "source.conformance"},
           {"interface I{fn f<T:Type+Copy+Drop>(x:T)->T;}component C:I{fn "
            "f<T:Type+Copy+Drop>(x:T)->T{return x;}}",
            "source.unsupported"},
       })
    refuses(prefix + source, code);
  refuses(prefix + "enum Opt<T:Type>{Some(T),None()}fn "
                   "forget<T:Type>(o:Opt<T>)->(){consume o;return ();}",
          "source.type");
  refuses(prefix + "interface Eat<X:Type>{type T;fn eat(x:X)->();}component "
                   "Sink<T:Type>:Eat<T>{type T=();fn eat(x:T)->(){consume "
                   "x;return ();}}",
          "source.shadow");
  refuses(
      prefix +
          "interface I{fn f()->bool;}fn unused<T:Type>()->bool{return I::f();}",
      "source.call");
  refuses(prefix + "interface I{type State;}fn "
                   "unused<T:Type>(x:I::State)->I::State{return x;}",
          "source.generic");
  refuses(prefix +
              "interface I{type State;}component C<T:Type>:I{type State=T;}fn "
              "unused<T:Type>(x:C::State)->C::State{return x;}",
          "source.generic");
  refuses(prefix + "interface I{struct R{pub x:bool}}", "source.syntax");
  refuses(prefix + "interface I{}component C:I{enum E{A()}}", "source.syntax");
  refuses(prefix + "interface I{type State;}struct Wrap<C:I>{pub "
                   "s:C::State}component K:I{type State=Wrap<K>;}",
          "source.cycle");
  refuses(prefix + R"(
interface Mix{math fn mix(a:Fr,b:Fr)->Fr;}
component Add:Mix{math fn mix(a:Fr,b:Fr)->Fr{return a+b;}}
math fn keep<C:Mix>(x:Fr,y:Fr)->Fr{let t=C::mix(x,y);return x;}
protocol Run roles(A,B)(x:Fr@A,y:Fr@B)->(r:Fr@A){return(r=keep<Add>(x,y));}
)",
          "source.roles");
  refuses(prefix + "struct Local:Copy+Drop {}protocol Run "
                   "roles(P,V)()->(r:Local@P){let x=Local{};return(r=x);}",
          "source.permission");
  check(prefix + "struct Box<N:nat>{pub x:[Fr;N]}fn "
                 "id<N:nat,M:nat>(x:Box<N+M>)->Box<M+N>{return x;}fn "
                 "useIt<N:nat>(x:Box<N>)->Box<N+0>{return id<N,0>(x);}");
  check(prefix + "math fn zero<F:Field>()->F{return 0;}math fn "
                 "add(x:Fr)->Fr{return zero()+x;}");
  check(prefix + R"(
interface A{type Out;}
math fn identity<C:A>(x:C::Out)->C::Out where Copy(C::Out),Drop(C::Out){return x;}
protocol Shared<G:Group> roles(P,V)(x:G::Scalar@(P,V))->(r:G::Scalar@(P,V)) where Share(G::Scalar){return(r=x);}
)");
  check(prefix + R"(
interface I<F:Field>{type Out:Field;fn f(x:Out)->Out where Wire(Out);}
component K<F:Field>:I<F>{type Out:Field=F;fn f(x:Out)->Out where Wire(Out){return x;}}
)");
  check(prefix + R"(
interface I<T:Type>{fn f(x:T)->T where Wire(T);}
component K<G:Group>:I<G::Scalar>{fn f(x:G::Scalar)->G::Scalar where Wire(G::Scalar){return x;}}
)");
  refuses(prefix + R"(
interface I<T:Type>{fn f(x:T)->T;}
component K<G:Group>:I<G::Scalar>{fn f(x:G::Scalar)->G::Scalar where Wire(G::Scalar){return x;}}
)",
          "source.conformance");
  check(prefix + R"(
interface I{type S:Field;fn f(x:S)->S where Wire(S);}
component K<F:Field>:I{type S:Field=F;fn f(x:S)->S where Wire(S){return x;}}
component Concrete:I{type S:Field=Fr;fn f(x:S)->S where Wire(S){return x;}}
interface J{type S:Group;fn f(x:S)->S where Wire(S);}
component L<G:Group>:J{type S:Group=G;fn f(x:S)->S where Wire(S){return x;}}
)");
  refuses(prefix + R"(
interface I{type S:Field;fn f(x:S)->S;}
component K<F:Field>:I{type S:Field=F;fn f(x:S)->S where Wire(S){return x;}}
)",
          "source.conformance");
  refuses(prefix +
              "struct Token:Drop{}fn f()->bool where Copy(Token){return true;}",
          "source.permission");
  auto boxedScalar = original(prefix + R"(
domain Curve=group("bls12-381.g1");
struct Box<G:Group>{pub item:G::Scalar}
protocol Run<G:Group> roles(P,V)(b:Box<G>@P)->(r:Box<G>@V)
where Share(G::Scalar),Wire(G::Scalar){let r=send P->V(b);return(r=r);}
entry Demo=Run<Curve>;
)");
  must(compileEntry(boxedScalar));
  check(prefix + R"(
fn need<T:Type+Wire>(x:T)->T{return x;}
fn mk<G:Group>(x:G::Scalar)->G::Scalar{return x;}
fn f<G:Group>(x:G::Scalar)->G::Scalar where Wire(G::Scalar){return need(mk<G>(x));}
)");
  check(prefix + R"(
interface Src{type Out;}
interface Sink<X:Type+Copy+Drop>{fn put(x:X)->();}
fn pipe<A:Src,B:Sink<A::Out>>(x:A::Out)->() where Copy(A::Out),Drop(A::Out){return B::put(x);}
fn direct<T:Type,C:Sink<T>>(x:T)->() where Copy(T),Drop(T){return C::put(x);}
)");
  refuses(prefix + R"(
interface Src{type Out;}
interface Sink<X:Type+Copy+Drop>{fn put(x:X)->();}
fn pipe<A:Src,B:Sink<A::Out>>(x:A::Out)->(){return B::put(x);}
)",
          "source.permission");
  check(prefix + R"(
interface Limited<N:nat> where 1<=N {fn get()->bool;}
fn f<N:nat,C:Limited<N>>()->bool where 1<=N{return C::get();}
)");
  refuses(prefix + R"(
interface Limited<N:nat> where 1<=N {fn get()->bool;}
fn f<N:nat,C:Limited<N>>()->bool{return C::get();}
)",
          "source.bound");
  check(prefix + R"(
struct Box<T:Type+Copy>{pub value:T}
interface Sink<X:Type>{fn put(x:X)->();}
fn f<T:Type,C:Sink<Box<T>>>(x:Box<T>)->() where Copy(T){return C::put(x);}
)");
  check(prefix + R"(
interface I{type Out;fn f(x:Out)->Out where Wire(Out);}
fn g<A:I>(x:A::Out)->A::Out where Wire(A::Out){return A::f(x);}
)");
  refuses(prefix + R"(
interface I{type Out;fn f(x:Out)->Out where Wire(Out);}
fn g<A:I>(x:A::Out)->A::Out{return A::f(x);}
)",
          "source.permission");
  check(prefix + R"(
interface I<T:Type>{type Out;fn f(x:Out)->Out where Wire(Out);}
component K<T:Type>:I<T>{type Out=T;fn f(x:Out)->Out where Wire(Out){return x;}}
)");
  check(prefix + R"(
interface I<G:Group>{fn f(x:G::Scalar)->G::Scalar where Wire(G::Scalar);}
component K<Scalar:Group>:I<Scalar>{fn f(x:Scalar::Scalar)->Scalar::Scalar where Wire(Scalar::Scalar){return x;}}
interface Algebra{type Scalar:Field;}
math fn sq<C:Algebra>(x:C::Scalar)->C::Scalar{return x*x;}
)");
  auto scalarWire = original(prefix + R"(
domain Curve=group("bls12-381.g1");
protocol Run<G:Group> roles(P,V)(x:G::Scalar@P)->(r:G::Scalar@V)
where Share(G::Scalar), Wire(G::Scalar) {let r=send P->V(x);return(r=r);}
entry Demo=Run<Curve>;
)");
  must(compileEntry(scalarWire));
  check(prefix + R"(
fn sendable<G:Group>(x:G::Scalar)->G::Scalar where Wire(G::Scalar){return x;}
fn outer<H:Group>(x:H::Scalar)->H::Scalar where Wire(H::Scalar){return sendable<H>(x);}
)");
  refuses(prefix + R"(
fn sendable<G:Group>(x:G::Scalar)->G::Scalar where Wire(G::Scalar){return x;}
fn outer<H:Group>(x:H::Scalar)->H::Scalar{return sendable<H>(x);}
)",
          "source.permission");
  refuses(prefix + R"(
interface I<G:Group>{fn f(x:G::Scalar)->G::Scalar;}
component C<G:Group>:I<G>{fn f(x:G::Scalar)->G::Scalar where Wire(G::Scalar){return x;}}
)",
          "source.conformance");
  check(prefix + R"(
interface I<G:Group>{fn f(x:G::Scalar)->G::Scalar where Wire(G::Scalar);}
component C<G:Group>:I<G>{fn f(x:G::Scalar)->G::Scalar where Wire(G::Scalar){return x;}}
)");
  check(prefix + "protocol Run roles(P)()->(r:bool@P){let r @P "
                 "=true;return(r=r);}entry Demo=Run;");
  must(compileEntry(original(
      prefix + "fn f(x:Fr)->Fr{return x;}protocol Run "
               "roles(P)(x:Fr@P)->(r:Fr@P){return(r=f(x));}entry Demo=Run;")));
  refuses(prefix +
              "struct Secret:Copy+Drop+Share+Wire {pub x:bool}protocol "
              "Run<T:Type+Copy+Drop+Share+Wire> "
              "roles(P)(x:T@P)->(r:T@P){return(r=x);}entry Demo=Run<Secret>;",
          "source.permission");
  refuses(prefix +
              "struct Secret {x:bool}protocol Run<T:Type+Copy+Drop+Share+Wire> "
              "roles(P)(x:T@P)->(r:T@P){return(r=x);}entry Demo=Run<Secret>;",
          "source.permission");
  auto libraryCapture = must(capture({{"lib", R"(module lib;
        pub interface Boxed<F:Field>{type State;fn make(x:F)->State;fn open(x:State)->F;}
        pub component Box<F:Field>:Boxed<F>{type State=F;fn make(x:F)->State{return State(x);}fn open(x:State)->F{return unpack(x);}}
      )",
                                       "lib.zkc"},
                                      {"m", prefix + R"(
        use lib::{Boxed,Box};
        fn work<C:Boxed<Fr>>(x:Fr)->Fr{let state=C::make(x);return C::open(state);}
        protocol Run roles(P)(x:Fr@P)->(r:Fr@P){let r @P =work<Box<Fr>>(x);return(r=r);}entry Demo=Run;
      )",
                                       "m.zkc"}}));
  auto libraryProject = must(analyze(libraryCapture).checkedProject());
  auto libraryOriginal =
      must(prepareOriginal(must(closeEntry(libraryProject, "m::Demo"))));
  must(compileEntry(libraryOriginal));
  auto variantPrivacy = must(capture(
      {{"lib", "module lib;pub enum Ticket:Drop{Valid(bool)}", "lib.zkc"},
       {"m",
        "module m;use lib::{Ticket};fn peek(t:Ticket)->bool{return match t "
        "{Valid(x)=>{ x}};}",
        "m.zkc"}}));
  auto privateMatch = analyze(variantPrivacy).checkedProject();
  require(!privateMatch, "restricted variant payload crossed module authority");
  require(
      StringRef(toString(privateMatch.takeError())).contains("source.private"),
      "wrong private match refusal");
  auto inaccessible = must(capture(
      {{"lib", "module lib;pub struct Restricted:Copy {pub x:bool}", "lib.zkc"},
       {"m",
        "module m;use lib::{Restricted};fn bad(x:bool)->Restricted{return "
        "Restricted{x:x};}",
        "types.zkc"}}));
  auto rejected = analyze(inaccessible).checkedProject();
  require(!rejected, "private constructor crossed module");
  require(StringRef(toString(rejected.takeError())).contains("source.private"),
          "wrong privacy refusal");
  refuses(prefix + "interface I{type State;math fn bad(x:State)->State;}",
          "source.mode");
  refuses(prefix + "type Nonempty<N:nat> where 1<=N=[Fr;N];fn "
                   "bad<N:nat>(x:Nonempty<N>)->(){return ();}",
          "source.bound");
  refuses(prefix + "interface I<N:nat>{fn f()->bool;}component "
                   "C<N:nat>:I<N>{fn f()->bool where 1<=N{return true;}}",
          "source.bound");
  refuses(prefix + "interface I<T:Type>{fn f(x:T)->T;}component "
                   "C<T:Type>:I<T>{fn f(x:T)->T where Copy(T){return x;}}",
          "source.conformance");
  check(prefix + "interface I<N:nat>{fn f()->bool where 1<=N;}component "
                 "C<N:nat>:I<N>{fn f()->bool where 1<=N{return true;}}");
  check(prefix + "struct Token:Copy {}fn forward(t:Token)->Token{let "
                 "second=t;return second;}");
  check(prefix +
        "struct Token:Share {}fn forward(t:Token,go:bool)->Token{return if go "
        "{ t}else{stop \"reject\";};}");
  check(prefix +
        "math fn first<F:Field,N:nat,M:nat>(a:[F;N+M])->[F;M+N]{return a;}");
  refuses(
      prefix +
          "math fn first<F:Field,N:nat,M:nat>(a:[F;N+M])->[F;N*M]{return a;}",
      "source.type");
  auto indexed = original(
      prefix + "fn count<N:nat>()->index{return index<N+1>();}protocol Run "
               "roles(P)()->(r:index@P){let r @P "
               "=count<2>();return(r=r);}entry Demo=Run;");
  must(compileEntry(indexed));
  auto nestedConstructor = original(
      prefix + "enum Choice{A(Fr)}fn get(v:Choice)->Fr{return match v {A(x)=>{ "
               "x}};}fn nested(x:Fr)->Fr{return get(Choice::A(x));}protocol "
               "Run roles(P)(x:Fr@P)->(r:Fr@P){let r @P "
               "=nested(x);return(r=r);}entry Demo=Run;");
  must(compileEntry(nestedConstructor));
  refuses(prefix +
              "enum Secret:Copy+Drop+Share+Wire {A(bool)}protocol Run "
              "roles(P)(x:Secret@P)->(r:Secret@P){return(r=x);}entry Demo=Run;",
          "source.permission");
  refuses(prefix + "struct Copy {}", "source.name");
  refuses(prefix +
              "enum Secret:Copy+Drop+Share+Wire {A(bool)}fn "
              "make()->Secret{return Secret::A(true);}protocol Run "
              "roles(P,V)()->(){let x @P =make();let y=send P->V(x);return();}",
          "source.permission");
  refuses(prefix + "struct Token:Drop+Share+Wire {}fn make()->Token{return "
                   "Token{};}protocol Run roles(P,V)()->(){let x @P "
                   "=make();let y=send P->V(x);return();}",
          "source.permission");
  auto nestedAssociated = original(prefix + R"(
interface I{type Out;fn make()->Out;fn finish(x:Out)->();}
component C:I{type Out=();fn make()->Out{return Out(());}fn finish(x:Out)->(){consume x;return ();}}
struct Holder<A:I>{pub item:A::Out}
fn forward<A:I>()->(){let h=Holder<A>{item:A::make()};return A::finish(h.item);}
protocol Run roles(P)()->(){let done @P =forward<C>();return();}entry Demo=Run;
)");
  must(compileEntry(nestedAssociated));
  check(prefix + R"(
struct Wrapped<G:Group> where Wire(G::Scalar) {pub x:G::Scalar}
fn need<T:Type+Wire>(x:T)->T{return x;}
fn read<G:Group>(x:Wrapped<G>)->G::Scalar where Wire(G::Scalar){return need(x.x);}
)");
  auto emptyArray =
      original(prefix + "struct Token:Share {}fn empty()->[Token;0]{return "
                        "[];}protocol Run roles(P)()->(r:[Token;0]@P){let r @P "
                        "=empty();return(r=r);}entry Demo=Run;");
  auto emptySchema = must(json::parse(emptyArray.interfaceJson()));
  auto *emptyPort = emptySchema.getAsObject()
                        ->getArray("protocols")
                        ->front()
                        .getAsObject()
                        ->getArray("outputs")
                        ->front()
                        .getAsObject();
  require(emptyPort->getArray("native")->empty(),
          "zero array has physical storage");
  require(*emptyPort->getObject("schema")->getArray("permissions") ==
              json::Array{"Share"},
          "empty array lost element permissions");
  auto emptySource = check("module m;protocol Run roles(P,V)()->(x:()@V){let "
                           "x=send P->V(());return(x=x);}entry Demo=Run;");
  auto emptyClosed = closeEntry(emptySource, "m::Demo");
  require(!emptyClosed, "empty source message passed closure");
  bool located = false;
  handleAllErrors(emptyClosed.takeError(), [&](const DiagnosticError &error) {
    located = error.diagnostic().code == "source.wire" &&
              bool(error.diagnostic().primary);
  });
  require(located, "empty message refusal lost its source location");
  auto malformed = emptySchema;
  (*malformed.getAsObject())["format"] = "invalid.language-interface";
  std::string malformedBytes;
  raw_string_ostream(malformedBytes) << malformed;
  auto invalidInterface = checkInterface(emptyArray, malformedBytes);
  require(bool(invalidInterface), "unknown source interface tag accepted");
  consumeError(std::move(invalidInterface));
}
void layoutsAndCorrespondence() {
  auto layoutProject =
      check(prefix + "interface I{type Out;}component C:I{type "
                     "Out=Fr;}component D:I{type Out=Fr;}");
  Layouts checkedLayouts(layoutProject);
  for (Type malformed :
       {Type(Type::Kind::Array), Type(Type::Kind::Associated, "m::C::Out"),
        Type(Type::Kind::Record, "m::C::Out")}) {
    auto layout = checkedLayouts.get(malformed);
    require(!layout, "malformed public layout accepted");
    consumeError(layout.takeError());
  }
  Type malformedScalar(Type::Kind::Boolean, "m::C::Out");
  auto scalarLayout = checkedLayouts.get(malformedScalar);
  require(!scalarLayout, "structural layout accepted a nominal identity");
  consumeError(scalarLayout.takeError());
  Type forged(Type::Kind::Associated, "m::C::Out");
  forged.arguments = {Type(Type::Kind::Component, "m::D")};
  auto forgedLayout = checkedLayouts.get(forged);
  require(!forgedLayout,
          "associated layout accepted foreign component identity");
  consumeError(forgedLayout.takeError());

  auto aggregate = original(prefix + R"(
struct Pair<T:Type+Copy+Drop>{pub left:T,pub right:T}
protocol Run roles(P)(p:Pair<Fr>@P,u:()@P)->(q:Pair<Fr>@P,u:()@P){return(q=Pair<Fr>{right:p.left,left:p.right},u=u);}
entry Demo=Run;)");
  auto schema = must(json::parse(aggregate.interfaceJson()));
  auto &ports = *schema.getAsObject()
                     ->getArray("protocols")
                     ->front()
                     .getAsObject()
                     ->getArray("inputs");
  require(ports[0].getAsObject()->getArray("native")->size() == 2 &&
              ports[1].getAsObject()->getArray("native")->empty(),
          "aggregate and empty port layout differs");
  auto wrong = must(json::parse(aggregate.interfaceJson()));
  (*wrong.getAsObject()
        ->getArray("protocols")
        ->front()
        .getAsObject()
        ->getArray("inputs"))[0]
      .getAsObject()
      ->getObject("schema")
      ->getArray("fields")
      ->front()
      .getAsObject()
      ->operator[]("offset") = 1;
  std::string bytes;
  raw_string_ostream(bytes) << wrong;
  auto rejected = checkInterface(aggregate, bytes);
  require(bool(rejected), "forged field offset accepted");
  consumeError(std::move(rejected));
  mutation(aggregate, [](auto module) {
    auto *ret = first(module, "protocol.return");
    auto a = ret->getOperand(0), b = ret->getOperand(1);
    ret->setOperands({b, a});
  });
  auto local = original(prefix + R"(
math fn twice<F:Field>(x:F)->F{return x+x;}
math fn outer(x:Fr)->Fr{return twice(x);}
fn choose(x:Fr,go:bool)->Fr {let y=outer(x);return if go { y}else{ x};}
protocol Run roles(P)(x:Fr@P,go:bool@P)->(r:Fr@P){let r @P =choose(outer(x),go);return(r=r);}entry Demo=Run;)");
  must(compileEntry(local));
  auto sharedMath = original(prefix + R"(
    enum Choice { Some(Fr), None() }
    math fn pair(x:Fr)->(Fr,Fr) { return (x,x+1); }
    fn choose(x:Fr,b:bool)->Fr {
      let value=if b  { let p=pair(x);  Choice::Some(p.1) }
                else {  Choice::None() };
      return match value  {
        Some(y)=>{let p=pair(y);  p.0},
        None()=>{let p=pair(x);  p.1}
      };
    }
    protocol Run roles(P)(x:Fr@P,b:bool@P)->(a:Fr@P,c:Fr@P) {
      let a=pair(x);
      let c @P =choose(x,b);
      return(a=a.1,c=c);
    }
    entry Demo=Run;
  )");
  must(compileEntry(sharedMath));
  mutation(sharedMath, [](mlir::ModuleOp module) {
    auto *realization = first(module, "local.realize");
    auto *duplicate = realization->clone();
    duplicate->setAttr("sym_name", mlir::StringAttr::get(module.getContext(),
                                                         "second_realization"));
    realization->getBlock()->push_back(duplicate);
    bool changed = false;
    module.walk([&](mlir::Operation *op) {
      if (!changed && op->getName().getStringRef() == "local.apply") {
        op->setAttr("callee", mlir::FlatSymbolRefAttr::get(
                                  module.getContext(), "second_realization"));
        changed = true;
      }
    });
    require(changed, "duplicate realization mutation found no call");
  });
  require(local.bytes().contains("local.realize") &&
              local.bytes().contains("func.call"),
          "math helper was specialized into a local body");
  mutation(local, [](auto module) {
    auto *realization = first(module, "local.realize");
    auto helper = realization->getAttr("helper");
    mlir::Attribute replacement;
    module.walk([&](mlir::Operation *op) {
      if (op->getName().getStringRef() == "func.call" &&
          op->getAttr("callee") != helper)
        replacement = op->getAttr("callee");
    });
    require(bool(replacement), "missing alternative math helper");
    realization->setAttr("helper", replacement);
  });
  mutation(local, [](auto module) {
    auto *realization = first(module, "local.realize");
    auto *duplicate = realization->clone();
    duplicate->setAttr("sym_name", mlir::StringAttr::get(module.getContext(),
                                                         "unused_realization"));
    realization->getBlock()->push_back(duplicate);
  });
  mutation(local, [](auto module) {
    auto *branch = first(module, "local.if");
    auto &a = branch->getRegion(0).front();
    a.back().setOperand(0, a.getArgument(0));
  });
  mutation(local, [](auto module) {
    first(module, "local.apply")
        ->setAttr("site",
                  mlir::StringAttr::get(module.getContext(), "different"));
  });
  auto variant = original(prefix + R"(
enum Choice{A(Fr),B(Fr)}
fn make(x:Fr)->Choice{return Choice::A(x);}
fn get(v:Choice)->Fr{return match v {A(x)=>{ x},B(x)=>{ x}};}
protocol Run roles(P)(x:Fr@P)->(r:Fr@P){let v @P =make(x);let y @P =get(v);return(r=y);}entry Demo=Run;)");
  mutation(variant, [](auto module) {
    first(module, "local.variant_inject")
        ->setAttr("alternative",
                  mlir::StringAttr::get(module.getContext(), "B"));
  });
  check(prefix + "fn singleton(x:Fr)->(Fr,){return(x,);}");
  // Representation checking owns nominal permission promises, even for an
  // otherwise unused component. Semantic queries may trust checked metadata.
  refuses(prefix + R"(
struct Token:Drop{}
interface I{type Out:Copy+Drop;}
component C:I{type Out:Copy+Drop=Token;}
)",
          "source.permission");
  auto nestedRepresentation = check(prefix + R"(
interface I{type In:Copy+Drop;type Out:Copy+Drop;}
component C:I{type In:Copy+Drop=bool;type Out:Copy+Drop=(In,bool);}
fn identity(x:C::Out)->C::Out{return x;}
)");
  Layouts nestedLayouts(nestedRepresentation);
  auto nested = must(nestedLayouts.get(
      nestedRepresentation.declarations().back().outputs.front().type));
  require(nested->permissions.copy && nested->leaves.size() == 2,
          "component representation retained an unresolved self projection");
  auto associatedLayout = original(prefix + R"(
interface Algebra {type Scalar:Field;}
component BLS:Algebra {type Scalar:Field=Fr;}
struct Box<C:Algebra> {pub value:C::Scalar}
fn get<C:Algebra>(box:Box<C>)->C::Scalar {return box.value;}
protocol Run roles(P)(box:Box<BLS>@P)->(r:Fr@P){let r @P =get<BLS>(box);return(r=r);}entry Demo=Run;)");
  must(compileEntry(associatedLayout));
  auto loop = original(prefix + R"(
fn count(n:index,x:Fr)->Fr{let mut s:Fr=0;for _ in 0..n{s=s+x;}return s;}
protocol Run roles(P)(n:index@P,x:Fr@P)->(r:Fr@P){let r @P =count(n,x);return(r=r);}entry Demo=Run;)");
  mutation(loop, [](auto module) {
    auto *op = first(module, "local.for");
    auto low = op->getOperand(0), high = op->getOperand(1);
    op->setOperand(0, high);
    op->setOperand(1, low);
  });
  auto guard = original(prefix + R"(
fn guarded(go:bool)->(){require go;return ();}
protocol Run roles(P)(go:bool@P)->(){let ignored @P =guarded(go);return();}entry Demo=Run;)");
  mutation(guard,
           [](auto module) { first(module, "protocol.local_call")->erase(); });
  mutation(guard, [](auto module) {
    auto *stop = first(module, "local.stop");
    stop->setAttr("reason",
                  mlir::StringAttr::get(module.getContext(), "abort"));
  });
  mutation(guard, [](auto module) {
    auto *branch = first(module, "local.if");
    mlir::Region temporary;
    temporary.takeBody(branch->getRegion(0));
    branch->getRegion(0).takeBody(branch->getRegion(1));
    branch->getRegion(1).takeBody(temporary);
  });
  mutation(guard, [](auto module) { first(module, "local.if")->erase(); });
  auto inferred = original(prefix + R"(
fn identity(x:Fr)->Fr{return x;}
protocol Run roles(P,V)(x:Fr@(P,V))->(){let unused@P=identity(x);return ();}
entry Demo=Run;)");
  mutation(inferred, [](auto module) {
    first(module, "protocol.local_call")
        ->setAttr("role", mlir::StringAttr::get(module.getContext(), "V"));
  });
  auto custodyVariant = original(prefix + R"(
enum Choice:Drop {unpack(), Other(Fr)}
fn get()->Fr{let v=Choice::unpack();return match v {Other(x)=>{ x},unpack()=>{let zero:Fr=0; zero}};}
protocol Run roles(P)()->(r:Fr@P){let r @P =get();return(r=r);}entry Demo=Run;)");
  must(compileEntry(custodyVariant));
  mutation(custodyVariant, [](auto module) {
    first(module, "local.exec.resource_unit_consume")->erase();
  });
  auto nominal = original(prefix + R"(
struct Tok<N:nat>:Drop {}
struct Holder<N:nat>{pub token:Tok<N+1>}
fn wrap()->Holder<1>{return Holder<1>{token:Tok<2>{}};}
fn finish(h:Holder<1>)->(){let t=h.token;consume t;return ();}
protocol Run roles(P)()->(){let h @P =wrap();let done @P =finish(h);return();}entry Demo=Run;)");
  must(compileEntry(nominal));
  auto resource = original(prefix + R"(
interface I{type State;fn make()->State;fn done(x:State)->();}
component C:I{type State=();fn make()->State{return State(());}fn done(x:State)->(){consume x;return ();}}
fn forward<T:I>()->(){let x=T::make();return T::done(x);}
protocol Run roles(P)()->(){let r @P =forward<C>();return();}entry Demo=Run;)");
  require(resource.bytes().contains("resource_unit"),
          "empty associated resource lost custody");
  must(compileEntry(resource));
  mutation(resource, [](auto module) {
    first(module, "local.exec.resource_unit_consume")->erase();
  });
}
void sourceNotation() {
  original(
      "module m;math fn pick(x:[bool;2])->bool{return x[1];}protocol Run "
      "roles(P)(x:[bool;2]@P)->(r:bool@P){return(r=pick(x));}entry Demo=Run;");
  for (StringRef bad : {"x[01]", "x.1", "x[value]"})
    refuses(
        ("module m;math fn pick(x:[bool;2])->bool{return " + bad + ";}").str(),
        "source.index");
  refuses(
      "module m;struct Rec{pub member:bool}math fn pick(x:Rec)->bool{return "
      "x[member];}",
      "source.index");
  refuses("module m;math fn pick(x:(bool,bool))->bool{return x[0];}",
          "source.index");
  refuses("module m;type Bad<N:nat*2>=[bool;N];", "source.syntax");
  refuses("module m;fn halt()->(){stop \"unknown\";}", "source.mode");
  for (StringRef reason :
       {"reject", "abort", "exhausted", "incomplete", "refused"})
    must(compileEntry(original(("module m;fn halt()->bool{stop \"" + reason +
                                "\";}protocol Run roles(P)()->(r:bool@P){let x "
                                "@P =halt();return(r=x);}entry Demo=Run;")
                                   .str())));
}
void bounds() {
  Limits termLimits;
  termLimits.typeNodes = 2;
  check("module m;type A=bool;type B=bool;type C=bool;type D=bool;",
        termLimits);
  refuses("module m;type A=(bool,bool,bool);", "source.limit", termLimits);
  std::string inherited = prefix + "interface Many<";
  for (unsigned i = 0; i < 64; ++i)
    inherited += (i ? "," : "") + std::string("N") + std::to_string(i) + ":nat";
  inherited += ">{";
  for (unsigned i = 0; i < 400; ++i)
    inherited += "fn f" + std::to_string(i) + "()->();";
  inherited += "}";
  Limits inheritedLimits;
  inheritedLimits.work = 50000;
  refuses(inherited, "source.limit", inheritedLimits);
  std::string expanded = prefix + "type A0=(bool,bool);";
  for (unsigned i = 1; i < 24; ++i)
    expanded += "type A" + std::to_string(i) + "=(A" + std::to_string(i - 1) +
                ",A" + std::to_string(i - 1) + ");";
  refuses(expanded, "source.limit");
  auto fanout = check("module m;protocol Run "
                      "roles(P)(z:[[[[();1024];1024];1024];1024]@P)->(){return("
                      ");}entry Demo=Run;");
  auto exploded = prepareOriginal(must(closeEntry(fanout, "m::Demo")));
  require(!exploded, "zero-leaf schema fanout escaped the work bound");
  require(StringRef(toString(exploded.takeError())).contains("source.limit"),
          "wrong schema fanout failure");
  Limits limits;
  limits.instances = 1;
  closureRefuses(
      prefix + "math fn id<F:Field>(x:F)->F{return x;}protocol Run "
               "roles(P)(x:Fr@P)->(r:Fr@P){return(r=id(x));}entry Demo=Run;",
      "source.limit", limits);
  limits = {};
  limits.naturalTerms = 1;
  refuses(prefix + "type A<N:nat,M:nat>=[Fr;N+M];", "source.limit", limits);
  limits = {};
  limits.naturalFactors = 1;
  refuses(prefix + "type A<N:nat,M:nat>=[Fr;N*M];", "source.limit", limits);
  limits = {};
  limits.aggregateLeaves = 1;
  refuses(prefix + "type A=[Fr;2];", "source.limit", limits);
  auto project =
      check(prefix + "struct Pair{pub a:Fr,pub b:Fr}" +
            "protocol Run roles(P)(x:Pair@P)->(y:Pair@P){return(y=x);}entry "
            "Demo=Run;");
  auto result = prepareOriginal(must(closeEntry(project, "m::Demo")), limits);
  require(!result, "aggregate leaf bound escaped emission");
  consumeError(result.takeError());
}
void staticDomains() {
  const std::string domains = prefix + R"(
    domain Kzg=commitment("multilinear.kzg.bls12-381/0");
    domain Transcript=transcript("merlin3.bls12-381.fr64be/0");
    domain Bn=field("bn254.fr");
    domain Ext=field("koala-bear.ext8-binomial3");
    domain Base=field("koala-bear");
    type Commitment<C:Commitment> = builtin("vector", C::ValueField);
    type TranscriptValues<T:Transcript> = builtin("vector", T::ChallengeField);
    struct Box<C:Commitment>{pub value:C::ValueField}
    math fn doubleValue<C:Commitment>(x:C::ValueField)->C::ValueField{return x+x;}
    fn total<C:Commitment>(xs:Commitment<C>)->C::ValueField{
      return kernel<C::ValueField>("vector.sum",xs);
    }
    interface Scheme{type Domain:Commitment;}
    component KzgScheme:Scheme{type Domain:Commitment=Kzg;}
    struct Configured<S:Scheme>{pub value:S::Domain::ValueField}
    fn configured<S:Scheme>(x:Configured<S>)->S::Domain::ValueField{
      return x.value;
    }
  )";
  auto selected = original(domains + R"(
    protocol Run roles(P,V)(x:Box<Kzg>@P,v:Commitment<Kzg>@P,
      t:TranscriptValues<Transcript>@P,c:Configured<KzgScheme>@P)
      ->(a:Fr@V,b:Fr@P,d:Fr@P){
      let a=send P->V(doubleValue<Kzg>(x.value));
      let b @P =total<Kzg>(v);let d @P =configured(c);
      return(a=a,b=b,d=d);
    }entry Demo=Run;
  )");
  must(compileEntry(selected));
  check(domains + R"(
    math fn canonical(x:Kzg::ValueField,y:Transcript::ChallengeField)->Fr{
      return x+y;
    }
    math fn chain(x:Bn::PairingG1::Scalar,y:m::Bn::PairingG2::Scalar)->Bn{
      return x+y;
    }
    math fn extension(x:Ext::BaseField)->Base{return x;}
    protocol Shared<C:Commitment> roles(P,V)
      (x:C::ValueField@P)->(r:C::ValueField@V)
      where Wire(C::ValueField),Share(C::ValueField){
      let r=send P->V(x);return(r=r);
    }
  )" + unit);
  for (const auto &body :
       {"fn bad<C:Commitment>(x:C)->C{return x;}",
        "type Bad<C:Commitment>=[C;2];", "type Bad<C:Commitment>=(C,Fr);",
        "type Bad=Kzg;", "type Bad=Kzg::Scalar;", "type Bad=Bn::ValueField;",
        "type Bad=Base::PairingG1;",
        "component Bad:Scheme{type Domain:Commitment=Fr;}"})
    refuses(domains + body + unit, "source.type");
  for (const auto &body :
       {"type Identity<T:Type>=T;type Bad=Identity<Kzg>;",
        "type Bad=Commitment<Fr>;", "type Bad=TranscriptValues<Kzg>;"})
    refuses(domains + body + unit, "source.generic");
  for (const auto &body : {"type Bad<C:Commitment+Copy>=bool;",
                           "type Bad<C:Commitment> where Copy(C)=bool;",
                           "type Bad where Wire(Kzg)=bool;",
                           "interface Bad{type Scheme:Commitment+Copy;}"})
    refuses(domains + body + unit, "source.permission");
  refuses(prefix + "domain Bad=commitment(\"unknown\");" + unit,
          "source.domain");
  refuses(prefix + "domain Bad=transcript(\"multilinear.kzg.bls12-381/0\");" +
              unit,
          "source.domain");
  refuses(domains + "type Bad=builtin(\"transcript\",Transcript);" + unit,
          "source.builtin");
  refuses(
      domains +
          "interface I{type Out;} component Wrong:I{type Out:Commitment=Kzg;}" +
          unit,
      "source.conformance");
  refuses(domains +
              "component Wrong:Scheme{type Domain:Transcript=Transcript;}" +
              unit,
          "source.conformance");
  refuses(domains + "interface Wrong{type D:NotASort;}" + unit, "source.type");
  refuses(prefix + "domain Bad=codec(\"unknown\");" + unit, "source.domain");
  refuses(prefix + "domain Bad=FIELD(\"bls12-381.fr\");" + unit,
          "source.domain");
  for (const auto &body : {"struct Bad{pub value:Kzg}", "enum Bad{Some(Kzg)}",
                           "protocol Bad roles(P)(x:Kzg@P)->(){return();}"})
    refuses(domains + body + unit, "source.type");
  refuses(domains + "type Bad=builtin(\"vector\",Kzg);" + unit,
          "source.builtin");
  must(compileEntry(original(domains + R"(
    interface Generic<C:Commitment>{fn get(x:C::ValueField)->C::ValueField;}
    component Selected<D:Commitment>:Generic<D>{
      fn get(x:D::ValueField)->D::ValueField{return x;}
    }
    component Forward<C:Commitment>:Scheme{type Domain:Commitment=C;}
    fn extract<C:Commitment>(x:Box<C>)->C::ValueField{return x.value;}
    fn invoke<C:Commitment,T:Generic<C>>(x:C::ValueField)->C::ValueField{
      return T::get(x);
    }
    interface View{type Domain:Commitment;
      fn identity(x:Domain::ValueField)->Domain::ValueField;}
    component NamedView:View{type Domain:Commitment=Kzg;
      fn identity(x:Domain::ValueField)->Domain::ValueField{return x;}}
    protocol Run<C:Commitment> roles(P)(x:Box<C>@P,
      c:Configured<Forward<C>>@P)->(r:C::ValueField@P)
      where Wire(C::ValueField){
      let a @P =extract(x);let b @P =invoke<C,Selected<C>>(a);
      let d @P =configured(c);return(r=b+d);
    }entry Demo=Run<Kzg>;
  )")));
  std::string longPath = "Bn";
  for (unsigned i = 0; i < 100; ++i)
    longPath += "::PairingG1::Scalar";
  refuses(domains + "type TooDeep=" + longPath + ";" + unit, "source.limit");
  const auto &codec = zkc::protocol::installedDomains().allCodecs().front();
  check(prefix + "domain Encoding=codec(\"" + codec.identity +
        "\"); type Tagged<C:Codec>=bool; fn "
        "pass(x:Tagged<Encoding>)->bool{return x;}" +
        unit);
  auto kzg = domainType("Commitment", "multilinear.kzg.bls12-381/0");
  auto fr = domainType("Field", "bls12-381.fr");
  require(must(domainMember(kzg, "ValueField")) == fr,
          "associated field did not use the canonical scalar kind");
  require(must(kernelArgument(kzg, "Commitment")) == kzg.domain,
          "closed commitment binding differs");
  auto wrong = kernelArgument(kzg, "Transcript");
  require(!wrong, "domain binding erased its sort");
  consumeError(wrong.takeError());
  auto symbolic = kzg;
  symbolic.symbolic = true;
  symbolic.domain = "parameter:C";
  auto other = symbolic;
  other.sort = "Transcript";
  require(typeIdentity(symbolic) != typeIdentity(other) && symbolic != other,
          "static domain identity erased its sort");
  auto project = check(prefix + unit);
  Layouts layouts(project);
  auto layout = layouts.get(kzg);
  require(!layout, "static domain acquired a runtime layout");
  consumeError(layout.takeError());
}

void nativeData() {
  const std::string library = prefix + R"(
    type Vector<F:Field> = builtin("vector", F);
    type Matrix<F:Field> = builtin("matrix", F);
    fn sum<F:Field>(v:Vector<F>)->F{return kernel<F>("vector.sum",v);}
    fn get<F:Field>(v:Vector<F>,i:index)->F{return kernel<F>("vector.get",v,i);}
  )";
  auto selected = original(library + R"(
    fn difference<F:Field>(a:Vector<F>,b:Vector<F>)->Vector<F>{
      return kernel<F>("vector.sub",a,b);
    }
    protocol Run roles(P,V)(a:Vector<Fr>@P,b:Vector<Fr>@P)->(r:Fr@V){
      let d @P =difference(a,b);
      let v=send P->V(d);
      let r @V =sum(v);
      return(r=r);
    }
    entry Demo=Run;
  )");
  must(compileEntry(selected));
  require(selected.bytes().contains("tensor<?x!algebra.field"),
          "dynamic vector did not retain native representation");
  mutation(selected, [](mlir::ModuleOp module) {
    mlir::Builder builder(module.getContext());
    module.walk([&](mlir::Operation *op) {
      if (op->getName().getStringRef() == "local.binding" &&
          op->getAttrOfType<mlir::StringAttr>("contract").getValue() ==
              "vector.sub")
        op->setAttr("contract", builder.getStringAttr("vector.add"));
      if (op->getName().getStringRef() == "algebra.exec.vector_sub") {
        mlir::OperationState state(op->getLoc(), "algebra.exec.vector_add");
        state.addOperands(op->getOperands());
        state.addTypes(op->getResultTypes());
        state.addAttributes(op->getAttrs());
        mlir::OpBuilder at(op);
        auto *replacement = at.create(state);
        op->replaceAllUsesWith(replacement->getResults());
        op->erase();
      }
    });
  });
  must(compileEntry(original(library + R"(
    fn parts<F:Field>(a:Vector<F>)->(Vector<F>,Vector<F>){
      return kernel<F>("vector.split",a);
    }
    fn length<F:Field>(a:Matrix<F>)->index{
      return kernel<F>("matrix.dimension",a;"1");
    }
    protocol Run roles(P)(a:Vector<Fr>@P,m:Matrix<Fr>@P)->(r:Fr@P,n:index@P){
      let p @P =parts(a);let s @P =sum(p.0);
      let dims @P =length(m);return(r=s,n=dims);
    }entry Demo=Run;
  )")));
  must(compileEntry(original(prefix + R"(
    type Values=builtin("sequence", Fr);
    fn singleton(x:Fr)->Values{
      let e=kernel<Fr>("sequence.empty");
      return kernel<Fr>("sequence.append",e,x);
    }
    fn first(xs:Values)->Fr{return kernel<Fr>("sequence.at",xs,0);}
    protocol Run roles(P,V)(x:Fr@P)->(r:Fr@V){
      let xs @P =singleton(x);let ys=send P->V(xs);
      let r @V =first(ys);return(r=r);
    }entry Demo=Run;
  )")));
  for (const auto &body : {"math fn bad<F:Field>(v:Vector<F>)->F{return "
                           "kernel<F>(\"vector.sum\",v);}",
                           "protocol Bad "
                           "roles(P)(v:Vector<Fr>@P)->(r:Fr@P){return(r=kernel<"
                           "Fr>(\"vector.sum\",v));}"})
    refuses(library + body + unit, "source.mode");
  refuses(library +
              "fn bad(v:Vector<Fr>)->Fr ! {} {return "
              "kernel<Fr>(\"vector.sum\",v);}" +
              unit,
          "source.effect");
  for (const auto &body :
       {"fn bad(v:Vector<Fr>)->Fr{return kernel<Fr>(\"vector.get\",v);}",
        "fn bad(v:Vector<Fr>)->Fr{return kernel<index>(\"vector.sum\",v);}",
        "fn bad(v:Vector<Fr>)->Fr{return "
        "kernel<Fr>(\"vector.get\",v,0;\"1\");}",
        "fn bad()->Fr{return kernel<Fr>(\"field.constant\";\"-1\");}",
        "fn bad()->Fr{return kernel<Fr>(\"not.installed\");}",
        "fn bad()->Fr{return kernel<Fr>(\"random.draw\");}",
        "fn bad()->Fr{return kernel<Fr>(\"transcript.challenge\");}"}) {
    refuses(library + body + unit, "source.kernel");
  }

  refuses(library + R"(
    fn bad<F:Field>(n:index)->F{return kernel<F>("poly.domain_root",n);}
  )" + unit,
          "source.kernel");
  must(compileEntry(original(prefix + R"(
    domain K=field("koala-bear");
    fn root(n:index)->K{return kernel<K>("poly.domain_root",n);}
    protocol Run roles(P)(n:index@P)->(r:K@P){let r @P =root(n);return(r=r);}
    entry Demo=Run;
  )")));
  refuses(prefix + "type Bad=builtin(\"vector\",index);" + unit,
          "source.builtin");
  refuses(prefix + "type Bad=builtin(\"resource_unit\");" + unit,
          "source.builtin");
  refuses(prefix + "struct Secret{x:Fr}type Bad=builtin(\"sequence\",Secret);" +
              unit,
          "source.builtin");
  refuses(library + R"(
    fn bad<F:Field>(x:F)->F{return kernel<F>("field.inverse",x);}
    math fn caller<F:Field>(x:F)->F{return bad(x);}
  )" + unit,
          "source.mode");
  // Native data is not automatically part of the total mathematical vocabulary.
  for (const auto &head : {"polynomial", "table", "point", "round"}) {
    const std::string data =
        "type Data=builtin(\"" + std::string(head) + "\",Fr);";
    refuses(prefix + data + "math fn bad(x:Data)->Data{return x;}" + unit,
            "source.mode");
    refuses(prefix + data +
                "struct Box{pub value:Data}math fn bad(x:Box)->Box{return x;}" +
                unit,
            "source.mode");
    refuses(prefix + data +
                "type Items=builtin(\"sequence\",Data);"
                "math fn bad(x:Items)->Items{return x;}" +
                unit,
            "source.mode");
  }
  must(compileEntry(original(library + R"(
    math fn identity<F:Field>(v:Vector<F>)->Vector<F>{return v;}
    protocol Run roles(P)(v:Vector<Fr>@P)->(r:Vector<Fr>@P){
      let r=identity(v);return(r=r);
    }entry Demo=Run;
  )")));
  closureRefuses(prefix + R"(
    type Data=builtin("polynomial",Fr);
    math fn identity<T:Type+Copy+Drop>(v:T)->T{return v;}
    protocol Run roles(P)(v:Data@P)->(r:Data@P){
      let r=identity(v);return(r=r);
    }entry Demo=Run;
  )",
                 "source.mode");
  closureRefuses(prefix + R"(
    type Data=builtin("polynomial",Fr);
    math fn identity<T:Type+Copy+Drop>(v:T)->T{return v;}
    fn work(v:Data)->Data{return identity(v);}
    protocol Run roles(P)(v:Data@P)->(r:Data@P){
      let r @P =work(v);return(r=r);
    }entry Demo=Run;
  )",
                 "source.mode");
  refuses(prefix + R"(
    struct Secret{pub value:Fr}
    fn bad(x:Secret)->index{return kernel<Secret>("sequence.length",x);}
  )" + unit,
          "source.kernel");
  // Full constructor and argument identities distinguish static instances.
  auto fr = Type(Type::Kind::Field, "bls12-381.fr");
  auto other = Type(Type::Kind::Field, "koala-bear");
  auto first = must(builtinType("vector", {fr}));
  auto second = must(builtinType("vector", {other}));
  require(typeIdentity(first) != typeIdentity(second),
          "native static identity erased the field");
  require(must(kernelArgument(first, "Type")) !=
              must(kernelArgument(second, "Type")),
          "native Type argument erased its application");
  auto constant = original(prefix + R"(
    fn literal()->Fr{return kernel<Fr>("field.constant";"7");}
    protocol Run roles(P)()->(r:Fr@P){let r @P =literal();return(r=r);}
    entry Demo=Run;
  )");
  must(compileEntry(constant));
}

} // namespace
int main() {
  staticDomains();
  nativeData();
  wireAuthority();
  typing();
  layoutsAndCorrespondence();
  sourceNotation();
  bounds();
  outs() << "types, permissions, static dispatch, local regions and "
            "correspondence checked\n";
}
