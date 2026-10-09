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
      } entry Demo=Run;
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
      } entry Demo=Run<F>;
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
      refuses(check(source + "entry Demo=Parent<0>;"), "source.bound");
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
      }entry Demo=Run;
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
  return cases.result();
}
