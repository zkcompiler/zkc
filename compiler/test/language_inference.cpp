#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
using namespace llvm;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
Expected<CheckedProject> check(StringRef source, const Limits &limits = {}) {
  auto captured = capture({{"m", "module m;" + source.str(), {}}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
const Declaration &declaration(const CheckedProject &project, StringRef name) {
  for (const auto &decl : project.declarations())
    if (decl.qualifiedName == name)
      return decl;
  throw std::runtime_error("missing declaration " + name.str());
}
void compile(StringRef source) {
  auto entry = take(closeEntry(take(check(source)), "m::Demo"));
  auto original = take(prepareOriginal(entry));
  for (bool simplify : {false, true})
    take(compileEntry(original, {simplify, false}));
}
} // namespace
int main() {
  zkc::test::Cases cases;
  const std::string identity = "fn id<T:Type>(x:T)->T{return x;}";
  for (StringRef value : {"x", "{x}", "{{x}}", "if b{x}else{x}", "{let y=x;y}",
                          "id({x})", "if b{stop \"reject\";}else{x}"})
    cases.run("generic argument composition: " + value, [&] {
      auto project = take(check(identity + "fn f(x:bool,b:bool){return id(" +
                                value.str() + ");}"));
      require(declaration(project, "m::f").outputs.front().type == Type{},
              "composed result did not infer bool");
    });
  for (StringRef value :
       {"if b{0}else{x}", "if b{x}else{0}", "id(if b{0}else{x})", "id([0,x])",
        "id([x,0])", "id([(0,x),(x,0)])", "id(if b{(0,x)}else{(x,0)})",
        "id((0+0)*x)", "id(id(0)*x)"}) {
    cases.run("symmetric aggregate inference: " + value, [&] {
      take(check(identity + "fn f<F:Field>(x:F,b:bool){return " + value.str() +
                 ";}"));
    });
  }
  cases.run("nested calls share partial type structure", [&] {
    take(check(identity + R"(
      fn pair<T:Type+Drop>(a:T,b:T)->T{return a;}
      fn f<F:Field>(x:F){return pair(id((0,x)),id((x,0)));}
      fn g<F:Field>(x:F)->(F,F){return id((id(0),x));}
      fn empty<F:Field>(x:[F;0]){return pair([],x);}
      fn lengths<N:nat>(x:[bool;N]){return id(x);}
    )"));
    take(check(identity + R"(
      fn f(x:bool,n:index){return (id(x),id(n));}
      fn pair<A:Type,B:Type>(a:A,b:B){return (a,b);}
      fn g<F:Field>(x:F){return pair<_,F>(true,0);}
    )"));
    refuses(check(identity + "fn f<T:Type>(x:T)->bool{return id(x);}"),
            "source.type");
  });
  cases.run("match payloads and lexical bindings supply types", [&] {
    compile(identity + R"(
      domain F=field("bls12-381.fr");
      enum Choice{Some(F),None()}
      fn f(c:Choice){return id(match c{None()=>{0},Some(x)=>{{x}}});}
      fn run(x:F){return f(Choice::Some(x));}
      protocol Run roles(P)(x:F@P)->(r:F@P){
        return run(x);
      }run Demo=Run;
    )");
  });
  cases.run(
      "inference preserves authored statement and definition boundaries", [&] {
        refuses(check(identity + "fn f()->index{let x=id(0);return x;}"),
                "source.inference");
        refuses(check(identity + "fn f()->index{return id({let x=0;x});}"),
                "source.inference");
        refuses(check(identity + "fn f(){return id(0);}"), "source.inference");
        refuses(check(identity + "fn f(){return id([]);}"), "source.inference");
        refuses(check(identity + R"(
      fn f(b:bool)->bool{
        return id({let x=if b{stop "reject";}else{stop "abort";};});
      }
    )"),
                "source.inference");
        refuses(check(identity + "fn f(x:bool){return id([x,()]);}"),
                "source.type");
        refuses(
            check(identity + "fn f(b:bool){return id(if b{true}else{()});}"),
            "source.type");
      });
  cases.run(
      "static equations are structural and associations only normalize forward",
      [] {
        take(check(R"(
      fn grow<N:nat>(xs:[bool;N+1]){return xs;}
      fn f(xs:[bool;4]){return grow<3>(xs);}
      fn both<N:nat>(x:[bool;N],y:[bool;N+1]){return (x,y);}
      fn g(x:[bool;2],y:[bool;3]){return both(x,y);}
    )"));
        refuses(check(R"(
      fn grow<N:nat>(xs:[bool;N+1]){return xs;}
      fn f(xs:[bool;4]){return grow(xs);}
    )"),
                "source.inference");
        refuses(check(R"(
      fn grow<N:nat>(xs:[bool;N+1]){return xs;}
      fn f(xs:[bool;4]){return grow<2>(xs);}
    )"),
                "source.type");
        refuses(check(R"(
      interface A{type Item:Copy+Drop;}
      fn get<C:A>(x:C::Item){return x;}
      fn f(x:bool){return get(x);}
    )"),
                "source.inference");
      });
  cases.run("type lookahead does not move values or execute effects", [&] {
    compile(identity + R"(
      struct Token:Drop {value:bool}
      fn f(x:Token,b:bool){
        return id(if b{x}else{x});
      }
      fn run(b:bool){
        let Token{value}=f(Token{value:b},b);return value;
      }
      protocol Run roles(P)(b:bool@P)->(r:bool@P){return run(b);}
      run Demo=Run;
    )");
    refuses(check(identity + R"(
      struct Token:Drop {}
      fn f(x:Token,b:bool){
        let y=id(if b{x}else{x});return (y,x);
      }
    )"),
            "source.move");
  });
  cases.run("helper contracts complete before use, independent of order", [] {
    for (bool reverse : {false, true}) {
      std::string leaf = "math fn leaf<F:Field>(x:F){return x+x;}";
      std::string caller = "math fn twice<F:Field>(x:F){return leaf(leaf(x));}";
      auto project = take(check(reverse ? leaf + caller : caller + leaf));
      auto &decl = declaration(project, "m::twice");
      require(decl.outputs.size() == 1 &&
                  decl.outputs[0].type == decl.inputs[0].type,
              "helper output was not inferred from its own definition");
    }
    compile(R"(
      domain F=field("bls12-381.fr");
      fn choose(x:F,go:bool){return if go{x}else{x+x};}
      protocol Run roles(P)(x:F@P,b:bool@P)->(r:F@P){
        return choose(x,b);
      } run Demo=Run;
    )");
    refuses(check("fn f(x:bool){return g(x);}fn g(x:bool){return f(x);}"),
            "source.cycle");
  });
  cases.run("inferred results never obtain types from callers", [] {
    refuses(check("fn f(){return 1;}fn caller()->index{return f();}"),
            "source.inference");
    refuses(check(R"(
      fn id<T:Type>(x:T)->T{return x;}
      fn caller()->index{return id(untyped());}
      fn untyped(){return 1;}
    )"),
            "source.inference");
    refuses(check("fn f(){return [];}"), "source.inference");
    refuses(check("fn f(){stop \"reject\";}"), "source.inference");
    refuses(check("interface A{fn f(x:bool);}"), "source.inference");
    refuses(check("fn f(x:bool)->index{return x;}"), "source.type");
    take(check("fn unit(){return ();}fn pair(x:bool){return (x,x);}"));
  });
  cases.run("static holes use arguments and expected results", [] {
    take(check(R"(
      fn value<T:Type,N:nat>(xs:[T;N])->[T;N]{return xs;}
      fn call(xs:[bool;2]){return value<_,2>(xs);}
      fn result<T:Type>(x:T)->T{return x;}
      fn contextual()->index{return result<_>(1);}
      interface Ops{fn get()->bool;}
      component Impl:Ops{fn get(){return true;}}
      fn invoke<T:Type+Drop,C:Ops>(x:T){return C::get();}
      fn caller(x:bool){return invoke<_,Impl>(x);}
    )"));
    refuses(check(R"(
      fn id<T:Type>(x:T)->T{return x;}
      fn bad(x:bool){return id<index>(x);}
    )"),
            "source.type");
    refuses(check("fn empty<N:nat>(){return ();}fn bad(){return empty<_>();}"),
            "source.inference");
    refuses(check("fn bad(x:_)->bool{return true;}"), "source.inference");
    refuses(check("fn id<T:Type>(x:T)->T{return x;}fn bad(x:bool){return "
                  "id<[_;2]>(x);}"),
            "source.inference");
  });
  cases.run("catalog requirements propagate with origins", [] {
    auto project = take(check(R"(
      fn wrapper<F:Field>(n:index){return root<F>(n);}
      fn root<F:Field>(n:index){return kernel<F>("poly.domain_root",n);}
    )"));
    for (StringRef name : {"m::root", "m::wrapper"}) {
      auto &decl = declaration(project, name);
      require(decl.capabilityBounds.size() == 1 &&
                  decl.capabilityBounds[0].inferred &&
                  decl.capabilityBounds[0].span.end >
                      decl.capabilityBounds[0].span.begin,
              "inferred catalog contract or origin absent");
    }
    refuses(check(R"(
      fn root<F:Field>(n:index) where () {
        return kernel<F>("poly.domain_root",n);
      }
    )"),
            "source.kernel");
    refuses(check(R"(
      domain F=field("bls12-381.fr");
      fn root(n:index){return kernel<F>("poly.domain_root",n);}
    )"),
            "source.kernel");
    compile(R"(
      domain F=field("koala-bear");
      fn root<T:Field>(n:index){return kernel<T>("poly.domain_root",n);}
      protocol Run<T:Field> roles(P)(n:index@P)->(r:T@P){
        return root<T>(n);
      } run Demo=Run<F>;
    )");
  });
  cases.run("natural preconditions are inferred and checked at closure", [] {
    auto project = take(check(R"(
      fn first<N:nat>(xs:[bool;N]){return xs[0];}
      fn caller<N:nat>(xs:[bool;N]){return first(xs);}
    )"));
    for (StringRef name : {"m::first", "m::caller"}) {
      auto &decl = declaration(project, name);
      require(decl.bounds.size() == 1 && decl.bounds[0].inferred &&
                  decl.bounds[0].lhs == Natural::constant(1),
              "missing inferred array bound");
    }
    refuses(check("fn first<N:nat>(xs:[bool;N]) where () {return xs[0];}"),
            "source.bound");
    refuses(check(R"(
      fn first<N:nat>(xs:[bool;N]){return xs[0];}
      fn bad(xs:[bool;0]){return first(xs);}
    )"),
            "source.bound");
  });
  cases.run("signature and specification bounds are complete before calls", [] {
    take(check(R"(
      type Checked<F:Field> where zkc::algebra::TwoAdicField(F)=F;
      fn pass<F:Field>(x:Checked<F>){return x;}
      fn caller<F:Field>(x:F){return pass(x);}
    )"));
    const std::string relation = "relation First(statement x:bool){return x;}";
    const std::string child = R"(
      protocol Child<N:nat> roles(P)(xs:[bool;N]@P)->(r:bool@P)
      spec{target claim=First(in.xs.0) accept out.r;}
      {return true;}
    )";
    const std::string parent = R"(
      protocol Parent<N:nat> roles(P)(xs:[bool;N]@P)->(r:bool@P){
        let r=Child(xs);return r;
      }
    )";
    for (bool reverse : {false, true}) {
      const auto source =
          relation + (reverse ? child + parent : parent + child);
      auto project = take(check(source));
      const auto &decl = declaration(project, "m::Parent");
      require(decl.bounds.size() == 1 && decl.bounds[0].inferred,
              "caller missed a specification precondition");
      refuses(check(source + "run Demo=Parent<0>;"), "source.bound");
    }
  });
  cases.run("resource contracts remain explicit", [] {
    refuses(check("fn twice<T:Type>(x:T){return (x,x);}"), "source.move");
    refuses(check("fn discard<T:Type>(x:T){return ();}"), "source.drop");
    take(check("fn twice<T:Type+Copy>(x:T){return (x,x);}"));
    take(check("fn discard<T:Type+Drop>(x:T){return ();}"));
    refuses(check(R"(
      protocol Transfer<T:Type> roles(P,V)(x:T@P)->(y:T@V){
        let y=send P->V(x); return y;
      }
    )"),
            "source.permission");
  });
  cases.run("component results and requirements obey interface promises", [] {
    take(check(R"(
      interface Roots<F:Field>{
        fn root(n:index)->F where zkc::algebra::TwoAdicField(F);
      }
      component Impl<F:Field>:Roots<F>{
        fn root(n:index){return kernel<F>("poly.domain_root",n);}
      }
    )"));
    refuses(check(R"(
      interface Roots<F:Field>{fn root(n:index)->F;}
      component Impl<F:Field>:Roots<F>{
        fn root(n:index){return kernel<F>("poly.domain_root",n);}
      }
    )"),
            "source.conformance");
    refuses(check(R"(
      interface A{fn f(x:bool)->bool !{};}
      component B:A{fn f(x:bool){require x;return x;}}
    )"),
            "source.effect");
    refuses(
        check("interface A{fn f()->bool;}component B:A{fn f(){return ();}}"),
        "source.conformance");
  });
  cases.run(
      "one protocol argument list preserves data and service identity", [] {
        const std::string source = R"(
      domain F=field("bls12-381.fr");
      protocol Draw<T:Field> roles(P)(a:Random<T>@P,x:bool@P,b:Random<T>@P)->(r:T@P){
        require @P x;
        let u=a.draw();let v=b.draw();return u+v;
      }
      protocol Run roles(P)(x:bool@P,coins:Random<F>@P)->(r:F@P){
        let alias=coins;let result=Draw(alias,x,coins);return result;
      }run Demo=Run;
    )";
        auto project = take(check(source));
        const auto &draw = declaration(project, "m::Draw");
        require(draw.inputOrder.size() == 3 && draw.inputs.size() == 1 &&
                    draw.services.size() == 2 &&
                    draw.inputOrder[1].kind ==
                        Declaration::InputSlot::Kind::Data,
                "source argument order was lost");
        const auto &body = *declaration(project, "m::Run").body;
        for (const auto &op : body.operations)
          if (auto *apply = std::get_if<ProtocolApplication>(&op.action))
            require(apply->services.size() == 2 &&
                        apply->services[0].index == apply->services[1].index,
                    "service alias acquired a new identity");
        compile(source);
        auto bad = source;
        bad.replace(bad.find("Draw(alias,x,coins)"), 19, "Draw(x,x,coins)");
        refuses(check(bad), "source.service");
      });
  cases.run("inference respects bounded work and call depth", [] {
    const std::string source = R"(
      fn a(x:bool){return b(x);}fn b(x:bool){return c(x);}
      fn c(x:bool){return x;}
    )";
    auto project = take(check(source));
    Limits limits;
    limits.work = project.checkedWork() - 1;
    refuses(check(source, limits), "source.limit");
    limits = {};
    limits.callDepth = 2;
    refuses(check(source, limits), "source.limit");
  });
  cases.run("independent statements do not rescan earlier bindings", [&] {
    auto work = [&](unsigned count) {
      std::string source = identity + "fn f(x:bool){";
      for (unsigned i = 0; i < count; ++i)
        source += "let v" + std::to_string(i) + "=id(x);";
      source += "return x;}";
      return take(check(source)).checkedWork();
    };
    require(work(400) < 3 * work(200),
            "type inference work grew with all previously bound names");
  });
  cases.run(
      "service patterns and implicit else preserve inference boundaries", [] {
        for (StringRef pattern : {"_", "(a,b)"})
          refuses(check("domain F=field(\"bls12-381.fr\");"
                        "protocol Run roles(P)(coins:Random<F>@P)->(x:bool@P){"
                        "let result @P ={let " +
                        pattern.str() + "=coins;true};return result;}"),
                  "source.service");
        take(check("fn f(b:bool)->bool{let u={if b{stop "
                   "\"reject\";}true};return u;}"));
      });
  cases.run("component and interface arities remain independent", [] {
    compile(R"(
      domain F=field("bls12-381.fr");domain G=group("bls12-381.g1");
      interface Increment<T:Field>{math fn add(x:T)->T;}
      component Plus<T:Field,H:Group>:Increment<T>{math fn add(x:T)->T{return x+1;}}
      math fn indirect<T:Field,C:Increment<T>>(x:T)->T{return C::add(x);}
      protocol Run roles(P)(x:F@P)->(r:F@P){
        return Plus::add<F,G>(x)+indirect<F,Plus<F,G>>(x);
      }run Demo=Run;
    )");
  });
  return cases.result();
}
