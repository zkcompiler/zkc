#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Dialect/Registry.h"
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
  zkc::registerNativeDialects(registry);
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
           {"fn bad(x:Fr)->Fr {let y=if true capture(){yield x;}else{yield "
            "x;};return y;}",
            "source.name"},
           {"enum Choice {A(Fr),B()} fn bad(v:Choice)->Fr {return match v "
            "capture(){A(x)=>{yield x;}};}",
            "source.match"},
           {"enum Choice {A(Fr),B()} fn bad(v:Choice)->Fr {return match v "
            "capture(){A(x)=>{yield x;},A(x)=>{yield x;}};}",
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
            "capture(t){yield t;}else{yield Token{};};}",
            "source.drop"},
           {"struct Token:Drop {} fn bad(t:Token,n:index)->(){let x=for i in "
            "0..n carry() capture(t){yield ();};return ();}",
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
  refuses(prefix + "protocol Run roles(P)()->(r:bool@P){local P let "
                   "r=true;return(r=r);}entry Demo=Run;",
          "source.mode");
  refuses(prefix + "fn f(x:Fr)->Fr{return x;}protocol Run "
                   "roles(P)(x:Fr@P)->(r:Fr@P){return(r=f(x));}entry Demo=Run;",
          "source.mode");
  closureRefuses(
      prefix + "struct Secret:Copy+Drop+Share+Wire {pub x:bool}protocol "
               "Run<T:Type+Copy+Drop+Share+Wire> "
               "roles(P)(x:T@P)->(r:T@P){return(r=x);}entry Demo=Run<Secret>;",
      "source.ingress");
  closureRefuses(
      prefix +
          "struct Secret {x:bool}protocol Run<T:Type+Copy+Drop+Share+Wire> "
          "roles(P)(x:T@P)->(r:T@P){return(r=x);}entry Demo=Run<Secret>;",
      "source.ingress");
  auto libraryCapture = must(capture({{"lib", R"(module lib;
        pub interface Boxed<F:Field>{type State;fn make(x:F)->State;fn open(x:State)->F;}
        pub component Box<F:Field>:Boxed<F>{type State=F;fn make(x:F)->State{return State(x);}fn open(x:State)->F{return unpack(x);}}
      )",
                                       "lib.zkc"},
                                      {"m", prefix + R"(
        use lib::{Boxed,Box};
        fn work<C:Boxed<Fr>>(x:Fr)->Fr{let state=C::make(x);return C::open(state);}
        protocol Run roles(P)(x:Fr@P)->(r:Fr@P){local P let r=work<Box<Fr>>(x);return(r=r);}entry Demo=Run;
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
        "capture(){Valid(x)=>{yield x;}};}",
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
        "capture(t){yield t;}else{stop \"reject\";};}");
  check(prefix +
        "math fn first<F:Field,N:nat,M:nat>(a:[F;N+M])->[F;M+N]{return a;}");
  refuses(
      prefix +
          "math fn first<F:Field,N:nat,M:nat>(a:[F;N+M])->[F;N*M]{return a;}",
      "source.type");
  auto indexed = original(
      prefix + "fn count<N:nat>()->index{return index<N+1>();}protocol Run "
               "roles(P)()->(r:index@P){local P let "
               "r=count<2>();return(r=r);}entry Demo=Run;");
  must(compileEntry(indexed));
  auto nestedConstructor = original(
      prefix +
      "enum Choice{A(Fr)}fn get(v:Choice)->Fr{return match v "
      "capture(){A(x)=>{yield x;}};}fn nested(x:Fr)->Fr{return "
      "get(Choice::A(x));}protocol Run roles(P)(x:Fr@P)->(r:Fr@P){local P let "
      "r=nested(x);return(r=r);}entry Demo=Run;");
  must(compileEntry(nestedConstructor));
  closureRefuses(
      prefix +
          "enum Secret:Copy+Drop+Share+Wire {A(bool)}protocol Run "
          "roles(P)(x:Secret@P)->(r:Secret@P){return(r=x);}entry Demo=Run;",
      "source.ingress");
  refuses(prefix + "struct Copy {}", "source.name");
  refuses(
      prefix +
          "enum Secret:Copy+Drop+Share+Wire {A(bool)}fn make()->Secret{return "
          "Secret::A(true);}protocol Run roles(P,V)()->(){local P let "
          "x=make();let y=send P->V(x);return();}",
      "source.ingress");
  refuses(prefix + "struct Token:Drop+Share+Wire {}fn make()->Token{return "
                   "Token{};}protocol Run roles(P,V)()->(){local P let "
                   "x=make();let y=send P->V(x);return();}",
          "source.permission");
  auto nestedAssociated = original(prefix + R"(
interface I{type Out;fn make()->Out;fn finish(x:Out)->();}
component C:I{type Out=();fn make()->Out{return Out(());}fn finish(x:Out)->(){consume x;return ();}}
struct Holder<A:I>{pub item:A::Out}
fn forward<A:I>()->(){let h=Holder<A>{item:A::make()};return A::finish(h.item);}
protocol Run roles(P)()->(){local P let done=forward<C>();return();}entry Demo=Run;
)");
  must(compileEntry(nestedAssociated));
  check(prefix + R"(
struct Wrapped<G:Group> where Wire(G::Scalar) {pub x:G::Scalar}
fn need<T:Type+Wire>(x:T)->T{return x;}
fn read<G:Group>(x:Wrapped<G>)->G::Scalar where Wire(G::Scalar){return need(x.x);}
)");
  auto emptyArray =
      original(prefix + "struct Token:Share {}fn empty()->[Token;0]{return "
                        "[];}protocol Run roles(P)()->(r:[Token;0]@P){local P "
                        "let r=empty();return(r=r);}entry Demo=Run;");
  auto emptySchema = must(json::parse(emptyArray.interfaceJson()));
  auto *emptyPort =
      emptySchema.getAsObject()->getArray("outputs")->front().getAsObject();
  require(emptyPort->getArray("native")->empty(),
          "zero array has physical storage");
  require(*emptyPort->getObject("schema")->getArray("permissions") ==
              json::Array{"Share"},
          "empty array lost element permissions");
  auto emptySource = check("module m;protocol Run roles(P,V)()->(x:()@V){let "
                           "x=send P->V(());return(x=x);}entry Demo=Run;");
  mlir::DialectRegistry registry;
  zkc::registerNativeDialects(registry);
  mlir::MLIRContext context(registry);
  auto erased = mlir::parseSourceString<mlir::ModuleOp>(R"(
module {
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{function_type = () -> (), input_roles = [], output_roles = [], roles = ["P", "V"], sym_name = "s1_m3_Run"}> ({
      "protocol.return"() : () -> ()
    }) : () -> ()
  }) : () -> ()
})",
                                                        &context);
  require(bool(erased) && succeeded(mlir::verify(*erased)),
          "erased unit-message module is invalid");
  auto absentMessage =
      compareOriginal(must(closeEntry(emptySource, "m::Demo")), *erased);
  require(!absentMessage,
          "independent comparison accepted an erased empty message");
  require(StringRef(toString(absentMessage.takeError()))
              .contains("source.correspondence"),
          "wrong empty-message comparison failure");
  auto oldVersion = emptySchema;
  (*oldVersion.getAsObject())["format"] = "zkc.language-interface/1";
  std::string oldBytes;
  raw_string_ostream(oldBytes) << oldVersion;
  auto oldInterface = checkInterface(emptyArray, oldBytes);
  require(bool(oldInterface), "obsolete source interface version accepted");
  consumeError(std::move(oldInterface));
  auto emptyMessage = prepareOriginal(
      must(closeEntry(check("module m;protocol Run roles(P,V)()->(x:()@V){let "
                            "x=send P->V(());return(x=x);}entry Demo=Run;"),
                      "m::Demo")));
  require(!emptyMessage, "empty source message silently erased");
  require(StringRef(toString(emptyMessage.takeError())).contains("source.wire"),
          "wrong empty-message refusal");
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
  auto &ports = *schema.getAsObject()->getArray("inputs");
  require(ports[0].getAsObject()->getArray("native")->size() == 2 &&
              ports[1].getAsObject()->getArray("native")->empty(),
          "aggregate and empty port layout differs");
  auto wrong = must(json::parse(aggregate.interfaceJson()));
  (*wrong.getAsObject()->getArray("inputs"))[0]
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
fn choose(x:Fr,go:bool)->Fr {let y=outer(x);return if go capture(x,y){yield y;}else{yield x;};}
protocol Run roles(P)(x:Fr@P,go:bool@P)->(r:Fr@P){local P let r=choose(outer(x),go);return(r=r);}entry Demo=Run;)");
  must(compileEntry(local));
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
fn get(v:Choice)->Fr{return match v capture(){A(x)=>{yield x;},B(x)=>{yield x;}};}
protocol Run roles(P)(x:Fr@P)->(r:Fr@P){local P let v=make(x);local P let y=get(v);return(r=y);}entry Demo=Run;)");
  mutation(variant, [](auto module) {
    first(module, "local.variant_inject")
        ->setAttr("alternative",
                  mlir::StringAttr::get(module.getContext(), "B"));
  });
  check(prefix + "fn singleton(x:Fr)->(Fr,){return(x,);}");
  auto associatedLayout = original(prefix + R"(
interface Algebra {type Scalar:Field;}
component BLS:Algebra {type Scalar:Field=Fr;}
struct Box<C:Algebra> {pub value:C::Scalar}
fn get<C:Algebra>(box:Box<C>)->C::Scalar {return box.value;}
protocol Run roles(P)(box:Box<BLS>@P)->(r:Fr@P){local P let r=get<BLS>(box);return(r=r);}entry Demo=Run;)");
  must(compileEntry(associatedLayout));
  auto loop = original(prefix + R"(
fn count(n:index,x:Fr)->Fr{let z:Fr=0;return for i in 0..n carry(s=z) capture(x){yield s+x;};}
protocol Run roles(P)(n:index@P,x:Fr@P)->(r:Fr@P){local P let r=count(n,x);return(r=r);}entry Demo=Run;)");
  mutation(loop, [](auto module) {
    auto *op = first(module, "local.for");
    auto low = op->getOperand(0), high = op->getOperand(1);
    op->setOperand(0, high);
    op->setOperand(1, low);
  });
  auto guard = original(prefix + R"(
fn guarded(go:bool)->(){require go;return ();}
protocol Run roles(P)(go:bool@P)->(){local P let ignored=guarded(go);return();}entry Demo=Run;)");
  mutation(guard,
           [](auto module) { first(module, "protocol.local_call")->erase(); });
  auto custodyVariant = original(prefix + R"(
enum Choice:Drop {unpack(), Other(Fr)}
fn get()->Fr{let v=Choice::unpack();return match v capture(){Other(x)=>{yield x;},unpack()=>{let zero:Fr=0;yield zero;}};}
protocol Run roles(P)()->(r:Fr@P){local P let r=get();return(r=r);}entry Demo=Run;)");
  must(compileEntry(custodyVariant));
  mutation(custodyVariant, [](auto module) {
    first(module, "local.exec.resource_unit_consume")->erase();
  });
  auto nominal = original(prefix + R"(
struct Tok<N:nat>:Drop {}
struct Holder<N:nat>{pub token:Tok<N+1>}
fn wrap()->Holder<1>{return Holder<1>{token:Tok<2>{}};}
fn finish(h:Holder<1>)->(){let t=h.token;consume t;return ();}
protocol Run roles(P)()->(){local P let h=wrap();local P let done=finish(h);return();}entry Demo=Run;)");
  must(compileEntry(nominal));
  auto resource = original(prefix + R"(
interface I{type State;fn make()->State;fn done(x:State)->();}
component C:I{type State=();fn make()->State{return State(());}fn done(x:State)->(){consume x;return ();}}
fn forward<T:I>()->(){let x=T::make();return T::done(x);}
protocol Run roles(P)()->(){local P let r=forward<C>();return();}entry Demo=Run;)");
  require(resource.bytes().contains("resource_unit"),
          "empty associated resource lost custody");
  must(compileEntry(resource));
  mutation(resource, [](auto module) {
    first(module, "local.exec.resource_unit_consume")->erase();
  });
}
void bounds() {
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
} // namespace
int main() {
  typing();
  layoutsAndCorrespondence();
  bounds();
  outs() << "types, permissions, static dispatch, local regions and "
            "correspondence checked\n";
}
