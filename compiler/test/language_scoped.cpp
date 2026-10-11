#include "../lib/Language/Effects.h"
#include "support/NativeCases.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/Project.h"
#include "llvm/Support/JSON.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
const std::string prelude = R"(module m;
domain Fr=field("koala-bear");
type Vector<F:Field>=builtin("vector",F);
fn get<F:Field>(xs:Vector<F>,i:index)->F=primitive("vector.get");
math fn apply_math<A:Type+Copy+Drop,B:Type+Copy+Drop>(x:A,body:math fn(A)->B)->B{return body(x);}
math fn forward_math<A:Type+Copy+Drop,B:Type+Copy+Drop>(x:A,body:math fn(A)->B)->B{return apply_math(x,body);}
fn apply<A:Type,B:Type>(x:A,body:fn(A)->B effects(stop))->B effects(stop){return body(x);}
fn forward<A:Type,B:Type>(x:A,body:fn(A)->B effects(stop))->B effects(stop){return apply(x,body);}
)";
Expected<CheckedProject> check(StringRef source) {
  auto captured = capture({{"m", prelude + source.str(), "scoped.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
void succeeds(StringRef source) {
  auto project = take(check(source));
  if (!project.entries().empty()) {
    auto closed = take(closeEntry(project, "m::Run"));
    for (const auto &decl : closed.declarations())
      if (decl.body) {
        require(decl.scopedInputs.empty(), "scoped signature survived closure");
        require(decl.body->scopedBindings.empty(),
                "scoped bindings survived closure");
        for (const auto &op : decl.body->operations)
          require(!std::holds_alternative<ScopedInvoke>(op.action),
                  "scoped invocation survived closure");
      }
  }
}
} // namespace
int main() {
  Cases cases;
  cases.run("symbolic effects specialize below explicit callback ceilings", [] {
    succeeds(R"(
fn precise(x:Fr)->Fr effects(){return forward(x,fn(y)=>y+1);}
protocol Demo roles(P)(x:Fr@P)->(r:Fr@P){return precise(x);}
run Run=Demo;)");
    refuses(check(R"(
fn bad(x:Fr)->Fr effects(){return forward(x,fn(y)=>{require y==1;y});}
)"),
            "source.effect");
  });
  cases.run("omitted callback ceilings retain dependencies through captures",
            [] {
              succeeds(R"(
fn invoke(x:Fr,f:fn(Fr)->Fr)->Fr effects(f){return f(x);}
fn adapter(x:Fr,f:fn(Fr)->Fr)->Fr effects(f){return invoke(x,fn(y)=>invoke(y,fn(z)=>f(z)));}
fn precise(x:Fr)->Fr effects(){return adapter(x,fn(y)=>y+1);}
protocol Demo roles(P)(x:Fr@P)->(r:Fr@P){return precise(x);}
run Run=Demo;)");
            });
  cases.run("output contracts are universally checked by callback identity", [] {
    for (
        auto source :
        {R"(fn bad(x:Fr,first:fn(Fr)->Fr,second:fn(Fr)->Fr)->Fr effects(first){return second(x);})",
         R"(fn bad(x:Fr,f:fn(Fr)->Fr)->Fr effects(f){require x==1;return f(x);})",
         R"(fn clean(x:Fr,f:fn(Fr)->Fr effects())->Fr effects(){return f(x);} fn bad(x:Fr,f:fn(Fr)->Fr)->Fr{return clean(x,f);})"}) {
      refuses(check(source), StringRef(source).contains("clean(x,f)")
                                 ? "source.scoped"
                                 : "source.effect");
    }
    succeeds(R"(
fn chain(x:Fr,first:fn(Fr)->Fr,second:fn(Fr)->Fr)->Fr effects(first,second){return second(first(x));}
fn unused(x:Fr,f:fn(Fr)->Fr)->Fr effects(){return x;}
fn renamed(x:Fr,callback:fn(Fr)->Fr)->Fr effects(callback){return callback(x);}
fn clean(x:Fr)->Fr effects(){return chain(x,fn(y)=>y,fn(y)=>unused(y,fn(z)=>{require z==1;z}));}
)");
  });
  cases.run("explicit kernel authoring retains its stopping envelope", [] {
    refuses(check(R"(
fn bad()->Fr effects(){return kernel<Fr>("field.constant";"1");}
)"),
            "source.effect");
    succeeds(R"(
fn good()->Fr effects(){return 1;}
)");
  });
  cases.run("eager argument evaluation is retained with unused callbacks", [] {
    refuses(check(R"(
fn unused(x:Fr,f:fn(Fr)->Fr)->Fr effects(){return x;}
fn argument(x:Fr)->Fr{require x==1;return x;}
fn bad(x:Fr)->Fr effects(){return unused(argument(x),fn(y)=>y);}
)"),
            "source.effect");
  });
  cases.run("effect grammar rejects legacy and foreign dependency syntax", [] {
    for (auto source : {R"(fn f(x:Fr)->Fr !{}{return x;})",
                        R"(fn f(x:Fr)->Fr effects(x){return x;})",
                        R"(fn f(x:Fr,b:fn(Fr)->Fr effects(b))->Fr{return x;})",
                        R"(fn f(x:Fr)->Fr effects(missing){return x;})",
                        R"(interface I{fn f(x:Fr)->Fr;})",
                        R"(fn f(x:Fr)->Fr effects() effects(){return x;})",
                        R"(fn f(x:Fr)->Fr where () effects(){return x;})"}) {
      refuses(check(source), StringRef(source).contains("effects() effects()")
                                 ? "source.syntax"
                                 : "source.effect");
    }
    refuses(check("fn f(x:Fr)->Fr effects(stop,stop){return x;}"),
            "source.duplicate");
    succeeds("fn effects(x:Fr)->Fr effects(){return x;}");
    succeeds(R"(
fn parameter(effects:Fr)->Fr{return effects;}
fn binding(x:Fr)->Fr{let effects=x;return effects;}
fn callback(x:Fr,effects:fn(Fr)->Fr)->Fr effects(effects){return effects(x);}
)");
    refuses(check("fn f<N:nat>(xs:[bool;N])->bool where 1<=N effects(){return "
                  "xs[0];}"),
            "source.effect");
  });
  cases.run("total callback references contribute no output effects", [] {
    auto project = take(check(R"(
fn local(x:Fr,body:fn(Fr)->Fr effects())->Fr effects(body){return body(x);}
fn mathematical(x:Fr,body:math fn(Fr)->Fr)->Fr effects(body){return body(x);}
)"));
    for (const auto &decl : project.declarations())
      if (decl.name == "local" || decl.name == "mathematical") {
        require(decl.effectAllowance == EffectSummary{} &&
                    decl.body->effects == EffectSummary{},
                "total callback retained a spurious effect dependency");
      }
    if (auto error = checkScopedElaboration(project))
      throw std::runtime_error(toString(std::move(error)));
  });
  cases.run("interface output dependencies preserve alpha-renamed slots", [] {
    succeeds(R"(
interface I{fn run(x:Fr,body:fn(Fr)->Fr)->Fr effects(body);}
module C:I{fn run(x:Fr,renamed:fn(Fr)->Fr)->Fr{return renamed(x);}}
fn through<T:I>(x:Fr,f:fn(Fr)->Fr)->Fr effects(f){return T::run(x,f);}
protocol Demo roles(P)(x:Fr@P)->(r:Fr@P){return through<C>(x,fn(y)=>y);}
run Run=Demo;)");
    refuses(check(R"(
interface I{fn run(x:Fr,a:fn(Fr)->Fr,b:fn(Fr)->Fr)->Fr effects(a);}
module C:I{fn run(x:Fr,a:fn(Fr)->Fr,b:fn(Fr)->Fr)->Fr{return b(x);}}
)"),
            "source.effect");
  });
  cases.run("module bodies refine their written output ceilings", [] {
    succeeds(R"(
interface I{fn run(x:Fr)->Fr effects();}
module C:I{fn run(x:Fr)->Fr effects(stop){return x;}}
fn through<T:I>(x:Fr)->Fr effects(){return T::run(x);}
protocol Demo roles(P)(x:Fr@P)->(r:Fr@P){return through<C>(x);}
run Run=Demo;)");
    refuses(check(R"(
interface I{fn run(x:Fr)->Fr effects();}
module C:I{fn run(x:Fr)->Fr effects(stop){require x==1;return x;}}
)"),
            "source.effect");
  });

  cases.run("generic Local apply and forwarding", [] {
    succeeds(R"(
protocol Demo roles(P)(x:Fr@P,a:Fr@P)->(r:Fr@P){return(r=forward(x,fn(y)=>y+a));}
run Run=Demo;)");
  });
  cases.run("existing reduction inside scoped callback", [] {
    succeeds(R"(
fn fold<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,step:fn(S,item:I)->S effects(stop) where item_from(item, rows))->S effects(stop)=finite("local.fold");
fn sum<I:Type+Copy+Drop>(rows:domain<I>,term:fn(item:I)->Fr effects(stop) where item_from(item, rows))->Fr effects(stop){return fold(rows,0,fn(state, item)=>state+term(item));}
reduction ∑=sum;
fn example(xs:Vector<Fr>,a:Fr)->Fr {
 return apply(a,fn(y)=>∑ x in xs, (x+a+y));
}
protocol Demo roles(P)(xs:Vector<Fr>@P,a:Fr@P)->(r:Fr@P){return example(xs,a);}
run Run=Demo;)");
  });
  cases.run(
      "scoped specialization retains joint authored and captured aliases", [] {
        auto project = take(check(R"(
fn twice(x:Fr,y:Fr,body:fn(Fr)->Fr effects(stop))->Fr effects(stop){return body(x)+y;}
fn dispatcher(x:Fr,y:Fr,body:fn(Fr)->Fr effects(stop))->Fr effects(stop){
 return twice(x,x,body)+twice(x,y,body);
}
protocol Demo roles(P)(x:Fr@P,y:Fr@P)->(r:Fr@P){return dispatcher(x,y,fn(v)=>v+y);}
run Run=Demo;
)"));
        auto closed = take(closeEntry(project, "m::Run"));
        if (auto error = checkScopedSpecialization(closed))
          throw std::runtime_error(toString(std::move(error)));
        unsigned variants = 0;
        for (const auto &declaration : closed.declarations())
          if (declaration.body && declaration.name == "twice") {
            ++variants;
            const auto &layout = declaration.closureLayout;
            if (layout.inputs == std::vector<unsigned>({0, 0}))
              require(layout.captures == std::vector<unsigned>{2} &&
                          declaration.inputs.size() == 3,
                      "independent captured value was merged with an authored "
                      "input");
            else
              require(layout.inputs == std::vector<unsigned>({0, 1}) &&
                          layout.captures == std::vector<unsigned>{1} &&
                          declaration.inputs.size() == 2,
                      "equal captured and authored places received different "
                      "ports");
          }
        require(variants == 2,
                "distinct alias partitions shared a specialization");
        bool changed = false;
        for (const auto &declaration : closed.declarations())
          if (declaration.body && declaration.name == "twice" &&
              declaration.inputs.size() == 3) {
            auto &layout = const_cast<Declaration &>(declaration).closureLayout;
            layout.captures.front() = 0;
            changed = true;
            break;
          }
        require(changed, "missing distinct-capture specialization");
        auto error = checkScopedSpecialization(closed);
        require(bool(error), "forged capture alias was accepted");
        consumeError(std::move(error));
      });
  cases.run(
      "long sequential let aliases close without expression recursion", [] {
        std::string program = "fn chain(x:Fr)->Fr effects(stop){let a0=x;";
        for (unsigned i = 1; i <= 150; ++i)
          program +=
              "let a" + std::to_string(i) + "=a" + std::to_string(i - 1) + ";";
        program += "return apply(a150,fn(y)=>y+a150);}";
        program += "protocol Demo roles(P)(x:Fr@P)->(r:Fr@P){return "
                   "chain(x);}run Run=Demo;";
        auto closed = take(closeEntry(take(check(program)), "m::Run"));
        if (auto error = checkScopedSpecialization(closed))
          throw std::runtime_error(toString(std::move(error)));
      });
  cases.run("many scoped calls share one body origin table", [] {
    std::string program =
        "fn wide(x:Fr,body:fn(Fr)->Fr effects(stop))->Fr effects(stop){";
    for (unsigned i = 0; i < 1200; ++i)
      program += "let a" + std::to_string(i) + "=apply(x,body);";
    program +=
        "return x;}protocol Demo roles(P)(x:Fr@P,a:Fr@P)->(r:Fr@P){return "
        "wide(x,fn(y)=>y+a);}run Run=Demo;";
    auto closed = take(closeEntry(take(check(program)), "m::Run"));
    if (auto error = checkScopedSpecialization(closed))
      throw std::runtime_error(toString(std::move(error)));
  });
  cases.run("protocol edge rejects coordinated forged input aliases", [] {
    auto closed = take(closeEntry(take(check(R"(
protocol Inner roles(P)(a:Fr@P,b:Fr@P)->(r:Fr@P){return a-b;}
protocol Demo roles(P)(x:Fr@P,y:Fr@P)->(r:Fr@P){let r=Inner(x,y);return r;}run Run=Demo;
)")),
                                  "m::Run"));
    bool changed = false;
    for (const auto &declaration : closed.declarations())
      if (declaration.body && declaration.name == "Inner") {
        auto &selected = const_cast<Declaration &>(declaration);
        selected.closureLayout.inputs = {0, 0};
        auto body = std::make_shared<Body>(*selected.body);
        selected.body = body;
        for (auto &op : body->operations)
          if (auto *math = std::get_if<MathValue>(&op.action))
            for (auto &operand : math->operands)
              if (operand.index == 1) {
                operand.index = 0;
                changed = true;
              }
      }
    require(changed, "protocol mutation did not reach the second operand");
    auto error = checkScopedSpecialization(closed);
    require(bool(error), "forged specialization accepted");
    require(toString(std::move(error)).find("source.scoped-specialization") !=
                std::string::npos,
            "wrong specialization refusal");
  });
  cases.run("truncated hidden input body is rejected before reading ports", [] {
    auto closed = take(closeEntry(take(check(R"(
fn twice(x:Fr,y:Fr,body:fn(Fr)->Fr effects(stop))->Fr effects(stop){return body(x)+y;}
protocol Demo roles(P)(x:Fr@P,a:Fr@P)->(r:Fr@P){return twice(x,x,fn(y)=>y+a);}run Run=Demo;
)")),
                                  "m::Run"));
    bool changed = false;
    for (const auto &declaration : closed.declarations())
      if (declaration.body && declaration.name == "twice") {
        require(declaration.inputs.size() == 3, "missing hidden input");
        auto body = std::make_shared<Body>(*declaration.body);
        const_cast<Declaration &>(declaration).body = body;
        body->values.resize(2);
        changed = true;
      }
    require(changed, "missing candidate body");
    auto error = checkScopedSpecialization(closed);
    require(bool(error), "forged specialization accepted");
    require(toString(std::move(error)).find("source.scoped-specialization") !=
                std::string::npos,
            "wrong specialization refusal");
  });
  cases.run("finite binder inside a scoped helper preserves capture layouts",
            [] {
              auto project = take(check(R"(
fn fold<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,step:fn(S,item:I)->S effects(stop) where item_from(item, rows))->S effects(stop)=finite("local.fold");
fn sum<I:Type+Copy+Drop>(rows:domain<I>,term:fn(item:I)->Fr effects(stop) where item_from(item, rows))->Fr effects(stop){return fold(rows,0,fn(state, item)=>state+term(item));}
reduction ∑=sum;
fn g(xs:Vector<Fr>,a:Fr,body:fn(Fr)->Fr effects(stop))->Fr effects(stop){let r=∑ x in xs,(x+a);return body(r);}
protocol Demo roles(P)(xs:Vector<Fr>@P,a:Fr@P,b:Fr@P)->(r:Fr@P){return g(xs,a,fn(y)=>y+b);}run Run=Demo;
)"));
              auto closed = take(closeEntry(project, "m::Run"));
              bool found = false;
              for (const auto &declaration : closed.declarations())
                if (declaration.name == "g" && declaration.body) {
                  require(declaration.inputs.size() == 3,
                          "helper did not gain a callback capture port");
                  found = true;
                }
              require(found, "missing closed helper");
              if (auto error = checkScopedSpecialization(closed))
                throw std::runtime_error(toString(std::move(error)));
            });
  cases.run(
      "loop carried state cannot alias an invariant callback capture", [] {
        auto project = take(check(R"(
fn iterate(x:Fr,n:index,body:fn(Fr)->Fr effects(stop))->Fr effects(stop){
 let mut state=x;for _ in 0..n {state=body(state);}return state;
}
protocol Demo roles(P)(x:Fr@P,n:index@P)->(r:Fr@P){return iterate(x,n,fn(y)=>y+x);}run Run=Demo;
)"));
        auto closed = take(closeEntry(project, "m::Run"));
        bool changed = false;
        for (const auto &decl : closed.declarations())
          if (decl.body && decl.name == "iterate") {
            auto body = std::make_shared<Body>(*decl.body);
            const_cast<Declaration &>(decl).body = body;
            for (auto &op : body->operations)
              if (auto *control = std::get_if<LocalControl>(&op.action)) {
                require(
                    control->regions.front()->inputs == 3 &&
                        control->regionLayouts.front().captures ==
                            std::vector<unsigned>{2},
                    "loop carried state was identified with initial invariant");
                require(control->regions.front()->results.back().index == 2,
                        "new invariant input missing from yield");
                control->regionLayouts.front().captures.front() = 1;
                changed = true;
              }
          }
        require(changed, "missing loop candidate");
        auto error = checkScopedSpecialization(closed);
        require(bool(error), "forged carried-state alias accepted");
        require(toString(std::move(error)).find("source.closure-inputs") !=
                    std::string::npos,
                "wrong loop alias refusal");
      });
  for (bool components : {false, true})
    for (const auto &control :
         {std::string("for"), std::string("if"), std::string("match")})
      cases.run(
          "hidden " + control + " input " +
              (components ? "participants" : "type"),
          [components, control] {
            std::string expression;
            if (control == "for")
              expression = "let mut state=x;for _ in 0..1 "
                           "{state=body(state);}return state;";
            else if (control == "if")
              expression = "return if flag {body(x)} else {x};";
            else
              expression =
                  "return match flag {Left(v)=>{body(v)},Right(v)=>{v}};";
            std::string flagType = control == "match" ? "Choice" : "bool";
            auto project = take(check(
                "enum Choice {Left(Fr),Right(Fr)} fn choose(x:Fr,flag:" +
                flagType +
                ",body:fn(Fr)->Fr "
                "effects(stop))->Fr effects(stop){" +
                expression +
                "}protocol Demo roles(P)(x:Fr@P,y:Fr@P,flag:" + flagType +
                "@P)"
                "->(r:Fr@P){return choose(x,flag,fn(v)=>v+y);}run Run=Demo;"));
            auto closed = take(closeEntry(project, "m::Run"));
            bool changed = false;
            for (const auto &decl : closed.declarations())
              if (decl.body && decl.name == "choose") {
                auto body = std::make_shared<Body>(*decl.body);
                const_cast<Declaration &>(decl).body = body;
                for (auto &op : body->operations)
                  if (auto *region = std::get_if<LocalControl>(&op.action)) {
                    auto copy = std::make_shared<Body>(*region->regions.back());
                    require(!region->regionLayouts.back().captures.empty(),
                            "missing hidden control capture");
                    auto port = region->regionLayouts.back().captures.back();
                    require(port < copy->inputs, "invalid hidden input");
                    if (components)
                      copy->values[port].components = {0};
                    else
                      copy->values[port].type = Type(Type::Kind::Index);
                    region->regions.back() = std::move(copy);
                    changed = true;
                  }
              }
            require(changed, "missing closed control region");
            auto error = checkScopedSpecialization(closed);
            require(bool(error), "forged hidden input accepted");
            require(toString(std::move(error))
                            .find("source.scoped-specialization") !=
                        std::string::npos,
                    "wrong hidden input refusal");
          });
  cases.run("control regions preserve function call depth", [] {
    std::string source = "fn f40(x:Fr)->Fr{return x;}";
    for (unsigned i = 0; i < 40; ++i)
      source += "fn f" + std::to_string(i) +
                "(x:Fr)->Fr{let mut s=x;for _ in 0..1 {s=f" +
                std::to_string(i + 1) + "(s);}return s;}";
    succeeds(source + "protocol Demo roles(P)(x:Fr@P)->(r:Fr@P)"
                      "{return f0(x);}run Run=Demo;");
  });
  cases.run("generic Math apply and forwarding", [] {
    succeeds(R"(
protocol Demo roles(P)(x:Fr@P,a:Fr@P)->(r:Fr@P){return(r=forward_math(x,fn(y)=>y+a));}
run Run=Demo;)");
  });
  cases.run("module nested scoped capture and record projections", [] {
    succeeds(R"(
interface Transform<F:Field>{fn adjust(x:F)->F effects();fn run(x:F,body:fn(F)->F effects(stop))->F effects(stop);}
module Increment<F:Field>:Transform<F>{
 fn adjust(x:F)->F effects(){return x+1;}
 fn run(x:F,body:fn(F)->F effects(stop))->F effects(stop){return forward(x,fn(y)=>body(adjust(y)));}
}
fn through<F:Field,C:Transform<F>>(x:F,body:fn(F)->F effects(stop))->F effects(stop){return C::run(x,body);}
struct Parameters<F:Field>{pub shift:F,pub table:Vector<F>}
protocol Demo roles(P,V)(x:Fr@(P,V),parameters:Parameters<Fr>@P,position:index@P)->(r:Fr@P){
 let result=through<Fr,Increment<Fr>>(x,fn(y)=>forward(y,fn(z)=>get(parameters.table,position)+z+parameters.shift));
 return(r=result);
}
run Run=Demo;)");
  });
  cases.run("Local callback has short circuit inside protocol", [] {
    succeeds(R"(
fn fail(x:bool)->bool effects(stop){require x;return x;}
protocol Demo roles(P)(x:bool@P)->(r:bool@P){return(r=apply(x,fn(y)=>false && fail(y)));}
run Run=Demo;)");
  });
  cases.run("multiple inputs and tuple destructuring", [] {
    succeeds(R"(
fn two(x:Fr,y:Fr,body:fn(Fr,Fr)->Fr effects())->Fr effects(){return body(x,y);}
fn pair(x:(Fr,Fr),body:fn((Fr,Fr))->Fr effects())->Fr effects(){return body(x);}
fn example(x:Fr,y:Fr)->Fr{return two(x,y,fn(a, b)=>a+b)+pair((x,y),fn((a,b))=>a-b);}
protocol Demo roles(P)(x:Fr@P,y:Fr@P)->(r:Fr@P){return(r=example(x,y));}run Run=Demo;)");
  });
  cases.run("empty input list, Unit pattern and trailing comma", [] {
    succeeds(R"(
fn zero(body:fn()->Fr effects())->Fr effects(){return body();}
fn unit(body:fn(())->Fr effects())->Fr effects(){return body(());}
fn one(x:Fr,body:fn(Fr)->Fr effects())->Fr effects(){return body(x);}
fn work(x:Fr)->Fr{return zero(fn()=>x)+unit(fn(())=>x)+one(x,fn(y,)=>y);}
protocol Demo roles(P)(x:Fr@P)->(r:Fr@P){return work(x);}run Run=Demo;
)");
  });
  cases.run("fun is an ordinary identifier", [] {
    succeeds(R"(
fn fun(x:Fr)->Fr{return x;}
protocol Demo roles(P)(x:Fr@P)->(r:Fr@P){return apply(x,fn(y)=>fun(y));}run Run=Demo;
)");
  });
  cases.run("scoped is an ordinary type name", [] {
    succeeds(R"(
type scoped=Fr;
fn identity(x:scoped)->scoped{return x;}
protocol Demo roles(P)(x:Fr@P)->(r:Fr@P){return identity(x);}
run Run=Demo;
)");
  });
  cases.run("scoped is an ordinary local and lambda binding name", [] {
    succeeds(R"(
fn bind(x:Fr)->Fr{let scoped=x;return apply(scoped,fn(y)=>y);}
protocol Demo roles(P)(x:Fr@P)->(r:Fr@P){return apply(bind(x),fn(scoped)=>scoped);}
run Run=Demo;
)");
  });
  cases.run("scoped is an ordinary function name", [] {
    succeeds(R"(
fn scoped(x:Fr)->Fr{return x;}
protocol Demo roles(P)(x:Fr@P)->(r:Fr@P){return scoped(x);}
run Run=Demo;
)");
  });
  for (const auto &source :
       {"fn f(body:scoped fn(Fr)->Fr effects())->Fr{return body(0);}",
        "math fn f(body:scoped math fn(Fr)->Fr)->Fr{return body(0);}",
        "fn f(rows:scoped domain<Fr>)->Fr{return 0;}",
        "domain fn f(xs:Vector<Fr>)->scoped domain<Fr>=domain(\"elements\");"})
    cases.run("reject obsolete signature " + std::string(source),
              [source] { refuses(check(source), "source.syntax"); });
  for (const auto &source :
       {"type Callback=fn(Fr)->Fr effects();", "type Rows=domain<Fr>;",
        "struct Holder{body:fn(Fr)->Fr effects()}",
        "struct Holder{rows:domain<Fr>}",
        "fn f()->fn(Fr)->Fr effects(){return fn(x)=>x;}",
        "fn f()->domain<Fr>{return [];}",
        "fn f(pair:(Fr,fn(Fr)->Fr effects()))->Fr{return 0;}",
        "fn f(body:fn(fn(Fr)->Fr effects())->Fr effects())->Fr{return 0;}"})
    cases.run("reject static signature in runtime type " + std::string(source),
              [source] { refuses(check(source), "source.name"); });
  for (const auto &[literal, code] :
       std::vector<std::pair<std::string, std::string>>{
           {"fun x=>x", "source.syntax"},
           {"fun(x)=>x", "source.syntax"},
           {"fn x=>x", "source.syntax"},
           {"fn(x y)=>x", "source.syntax"},
           {"fn(x)=>", "source.name"},
           {"fn(x) x", "source.syntax"},
           {"fn(,x)=>x", "source.name"}})
    cases.run(
        "reject malformed lambda " + literal, [literal = literal, code = code] {
          refuses(check("fn work(x:Fr)->Fr{return apply(x," + literal + ");}"),
                  code);
        });
  cases.run("affine explicit parameters and mutable callback state", [] {
    succeeds(R"(
struct Token:Drop {}
fn carry(x:Token,n:index)->Token{return forward(x,fn(y)=>{let mut state=y;for _ in 0..n {let old=state;consume old;state=Token{};}state});}
fn work(n:index)->bool{let value=carry(Token{},n);consume value;return true;}
protocol Demo roles(P)(n:index@P)->(r:bool@P){return work(n);}run Run=Demo;
)");
  });
  cases.run("Math Boolean callback inside protocol formula", [] {
    succeeds(R"(
protocol Demo roles(P,V)(x:bool@(P,V))->(r:bool@(P,V)){return true && apply_math(x,fn(y)=>y || false);}run Run=Demo;
)");
  });
  cases.run("unused contextual callback and all-stopping callback", [] {
    succeeds(R"(
fn ignore<A:Type+Drop,B:Type+Copy+Drop>(x:A,body:fn(A)->B effects(stop),fallback:B)->B effects(){return fallback;}
fn work(x:Fr)->Fr{return ignore(x,fn(_)=>{stop "reject";},x);}
protocol Demo roles(P)(x:Fr@P)->(r:Fr@P){return work(x);}run Run=Demo;
)");
  });

  cases.run("abstract Math callback captures survive wrapper summaries", [] {
    const std::string helpers = R"(
interface MathOps<F:Field>{math fn run(x:F,body:math fn(F)->F)->F;}
module Impl<F:Field>:MathOps<F>{math fn run(x:F,body:math fn(F)->F)->F{return body(x);}}
math fn g<F:Field,C:MathOps<F>>(x:F,y:F)->F{return C::run(x,fn(t)=>t+y);}
math fn h(x:Fr,y:Fr)->Fr{return g<Fr,Impl<Fr>>(x,y);}
)";
    for (const auto &call : {"h(x,y)", "g<Fr,Impl<Fr>>(x,y)"})
      refuses(check(helpers +
                    "protocol Demo "
                    "roles(P,V)(x:Fr@(P,V),y:Fr@P)->(r:Fr@(P,V)){return(r=" +
                    call + ");}run Run=Demo;"),
              "source.roles");
    succeeds(helpers + "protocol Demo "
                       "roles(P,V)(x:Fr@(P,V),y:Fr@P)->(r:Fr@P){return(r=h(x,y)"
                       ");}run Run=Demo;");
  });
  cases.run("callback after whole reassignment does not capture moved input",
            [] {
              succeeds(R"(
struct Token:Drop {}
struct Holder {pub v:Fr,pub t:Token}
fn f(x:Fr,c:bool,h:Holder)->Fr{
 let mut s=h;let old=s;
 return if c {s=Holder{v:x,t:Token{}};apply(x,fn(y)=>y+s.v)}
 else {s=Holder{v:x,t:Token{}};x};
}
fn run(x:Fr,c:bool)->Fr{return f(x,c,Holder{v:x,t:Token{}});}
protocol Demo roles(P)(x:Fr@P,c:bool@P)->(r:Fr@P){return run(x,c);}run Run=Demo;
)");
            });
  cases.run("always-stopping argument excludes unreachable callback capture",
            [] {
              refuses(check(R"(
fn g(a:Fr,b:Fr)->Fr{return a;}
fn f(x:Fr,a:Fr)->Fr{return apply(x,fn(y)=>g({stop "reject";},a));}
protocol Demo roles(P)(x:Fr@P,a:Fr@P)->(r:Fr@P){return f(x,a);}run Run=Demo;
)"),
                      "source.unreachable");
            });

  cases.run("formation summaries are sets across wide helper reuse", [] {
    std::string source = "math fn wide(x:Fr)->Fr{";
    for (unsigned i = 0; i < 256; ++i)
      source += "let a" + std::to_string(i) + "=x+x;";
    source += "return x;} math fn middle(x:Fr)->Fr{return wide(x);} math fn "
              "caller(x:Fr)->Fr{";
    for (unsigned i = 0; i < 256; ++i)
      source += "let a" + std::to_string(i) + "=middle(x);";
    source += "return x;}";
    auto captured = take(capture({{"m", prelude + source, "wide.zkc"}}));
    auto project = take(analyze(captured).checkedProject());
    for (const auto &decl : project.declarations())
      if (decl.name == "wide" || decl.name == "middle" || decl.name == "caller")
        require(decl.body->formationRequirements.size() == 1,
                "duplicate formation requirements accumulated");
    Limits limits;
    limits.work = project.checkedWork() - 1;
    refuses(analyze(captured, limits).checkedProject(), "source.limit");
    limits.work = project.checkedWork();
    take(analyze(captured, limits).checkedProject());
  });

  const std::vector<std::pair<std::string, std::string>> refusals = {
      {"protocol Bad roles(P)(body:fn(Fr)->Fr effects()@P)->(){return();}",
       "source.scoped"},
      {"protocol Bad roles(P)(body:math fn(Fr)->Fr@P)->(){return();}",
       "source.scoped"},
      {"protocol Bad roles(P)()->(body:fn(Fr)->Fr effects()@P){return();}",
       "source.scoped"},
      {"protocol Bad roles(P)()->(body:math fn(Fr)->Fr@P){return();}",
       "source.scoped"},
      {"protocol Bad roles(P)()->(rows:domain<Fr>@P){return();}",
       "source.scoped"},

      {"fn f(x:Fr,b:math fn(Fr)->Fr effects(stop))->Fr{return x;}",
       "source.effect"},
      {"fn f(x:Fr)->Fr{return apply_math(x,fn(y)=>get(([],),0));}",
       "source.type"},
      {"fn f(x:Fr,b:fn(Fr)->Fr effects())->Fr{return b;}", "source.scoped"},
      {"fn f(x:Fr)->Fr{let b=fn(y)=>y;return x;}", "source.scoped"},
      {"fn f(x:Fr)->Fr{let mut a=x;return apply(x,fn(y)=>{a=y;y});}",
       "source.scoped-capture"},
      {"fn unused<A:Type>(x:A,b:fn(A)->A effects())->A{return b(true);}",
       "source.type"},
      {"math fn f(x:Fr,b:fn(Fr)->Fr effects())->Fr{return b(x);}",
       "source.mode"},
      {"fn stop_value(x:Fr)->Fr effects(stop){stop \"reject\";} fn "
       "f(x:Fr)->Fr{return apply_math(x,fn(y)=>stop_value(y));}",
       "source.mode"},
      {"fn clean(x:Fr,b:fn(Fr)->Fr effects())->Fr effects(){return b(x);} fn "
       "stop_value(x:Fr)->Fr effects(stop){stop \"reject\";} fn "
       "f(x:Fr)->Fr{return "
       "clean(x,fn(y)=>stop_value(y));}",
       "source.effect"},
      {"fn f(x:Fr,b:fn(Fr)->Fr effects())->Fr{return apply_math(x,b);}",
       "source.scoped"},
      {"protocol Demo "
       "roles(P,V)(x:Fr@(P,V),a:Fr@P,b:Fr@V)->(r:Fr@P){return(r=apply(x,fn(y)=>"
       "y+a+b));}run Run=Demo;",
       "source.roles"},
      {"protocol Demo "
       "roles(P,V)(x:Fr@(P,V))->(r:Fr@(P,V)){return(r=apply(x,fn(y)=>y));}run "
       "Run=Demo;",
       "source.roles"},
      {"fn identity(x:Fr)->Fr{return x;} protocol Demo "
       "roles(P,V)(x:Fr@(P,V))->(r:Fr@P){return(r=apply_math(identity(x),fn(_)="
       ">0));}run Run=Demo;",
       "source.owner"},
      {"protocol Demo "
       "roles(P,V)(x:Fr@P,a:Fr@P,b:Fr@V)->(r:Fr@P){return(r=apply_math(x,fn(_)="
       ">{let dead=a+b;0}));}run Run=Demo;",
       "source.roles"},
      {"fn f(x:Fr)->Fr{return apply(x,fn((a,b))=>a+b);}", "source.type"},
      {"fn f(x:Fr)->Fr{return apply(x,fn(a, b)=>a+b);}", "source.scoped"},
      {"fn f(x:Fr)->Fr{return apply(x,fn(y)=>f(y));}", "source.cycle"},
      {"struct Token:Drop {} fn f(x:Fr,t:Token)->Fr{return "
       "apply(x,fn(y)=>{consume t;y});}",
       "source.scoped-capture"},
      {"struct Token:Copy {} fn f(x:Fr,t:Token)->Fr{return "
       "apply(x,fn(y)=>{consume t;y});}",
       "source.scoped-capture"},
      {"struct Token:Drop {} fn f(t:Token)->(Token,Token){return "
       "apply(t,fn(y)=>(y,y));}",
       "source.move"},
      {"protocol Demo roles(P)(x:Fr@P,coins:Random<Fr>@P)->(r:Fr@P){return "
       "apply(x,fn(y)=>y+coins.draw());}run Run=Demo;",
       "source.scoped-capture"},
      {"interface I{fn f(x:Fr,b:fn(Fr)->Fr effects())->Fr effects();}module "
       "C:I{fn f(x:Fr,b:fn(Fr)->Fr effects(stop))->Fr effects(stop){return "
       "b(x);}}",
       "source.conformance"},
      {"fn unused<A:Type+Copy+Drop>(x:A)->A{return apply_math(x,fn(y)=>{let "
       "bad:bool=y;y});}",
       "source.type"},
  };
  for (unsigned i = 0; i < refusals.size(); ++i)
    cases.run("scoped refusal " + std::to_string(i),
              [&] { refuses(check(refusals[i].first), refusals[i].second); });
  cases.run("scoped expansion respects closed instance and depth bounds", [] {
    auto project = take(check(R"(
protocol Demo roles(P)(x:Fr@P)->(r:Fr@P){return forward(x,fn(y)=>forward(y,fn(z)=>z+x));}run Run=Demo;
)"));
    Limits limits;
    limits.instances = 2;
    refuses(closeEntry(project, "m::Run", limits), "source.limit");
    limits = Limits{};
    limits.callDepth = 2;
    refuses(closeEntry(project, "m::Run", limits), "source.limit");
    limits = Limits{};
    limits.work = 1;
    auto error = checkScopedElaboration(project, limits);
    require(bool(error), "capture witness ignored lowered work bound");
    require(toString(std::move(error)).find("source.limit") !=
                std::string::npos,
            "wrong witness budget refusal");
  });
  cases.run("declaration inspection separates scoped and runtime inputs", [] {
    auto project =
        take(check("pub fn export_body(x:Fr,body:fn(Fr)->Fr "
                   "effects(stop))->Fr effects(stop){return body(x);}"));
    auto json = take(inspectDeclarations(project));
    require(StringRef(json).contains("\"scoped_inputs\"") &&
                StringRef(json).contains("\"scoped\"") &&
                StringRef(json).contains("\"stop\""),
            "scoped inspection contract missing");
  });
  cases.run("forwarded scoped selection mutation is rejected", [] {
    auto project = take(check(R"(
fn chain(x:Fr,first:fn(Fr)->Fr effects(stop),second:fn(Fr)->Fr effects(stop))->Fr effects(stop){return second(first(x));}
protocol Demo roles(P)(x:Fr@P,a:Fr@P,b:Fr@P)->(r:Fr@P){return chain(x,fn(y)=>y+a,fn(y)=>y*b);}run Run=Demo;
)"));
    auto closed = take(closeEntry(project, "m::Run"));
    bool changed = false;
    for (const auto &decl : closed.declarations())
      if (decl.body && decl.name == "chain") {
        auto &candidate = const_cast<Declaration &>(decl);
        std::swap(candidate.scopedArguments[0], candidate.scopedArguments[1]);
        changed = true;
      }
    require(changed, "missing selected chain");
    auto error = checkScopedSpecialization(closed);
    require(bool(error), "swapped static callback targets accepted");
    require(toString(std::move(error)).find("source.scoped-specialization") !=
                std::string::npos,
            "wrong static target refusal");
  });
  const std::string captured = R"(
protocol Demo roles(P)(x:Fr@P,a:Fr@P,b:Fr@P)->(r:Fr@P){return(r=forward(x,fn(y)=>{let dead=a+b;y+a-b}));}
run Run=Demo;)";
  for (bool specialized : {false, true})
    for (unsigned mutation = 0; mutation < 4; ++mutation)
      cases.run(
          std::string(specialized ? "specialized" : "authored") +
              " scoped call mapping mutation " + std::to_string(mutation),
          [&] {
            auto project = take(check(R"(
fn chain(x:Fr,first:fn(Fr)->Fr effects(stop),second:fn(Fr)->Fr effects(stop))->Fr effects(stop){return second(first(x));}
protocol Demo roles(P)(x:Fr@P,a:Fr@P,b:Fr@P)->(r:Fr@P){return chain(second=fn(y)=>y*b,x=x,first=fn(y)=>y+a);}run Run=Demo;
)"));
            auto closed = take(closeEntry(project, "m::Run"));
            auto declarations =
                specialized ? closed.declarations() : project.declarations();
            bool changed = false;
            for (const auto &decl : declarations)
              if (decl.name == "Demo" && decl.body) {
                auto body = std::make_shared<Body>(*decl.body);
                const_cast<Declaration &>(decl).body = body;
                for (auto &operation : body->operations)
                  if (operation.binding && operation.binding->scopedSource) {
                    auto &binding = *operation.binding;
                    if (mutation == 0)
                      binding.scopedSource.reset();
                    if (mutation == 1)
                      std::swap(binding.argumentOrder[0],
                                binding.argumentOrder[1]);
                    if (mutation == 2)
                      std::swap(binding.scopedArguments[0],
                                binding.scopedArguments[1]);
                    if (mutation == 3) {
                      std::swap(binding.scopedArguments[0],
                                binding.scopedArguments[1]);
                      if (!specialized) {
                        auto &call = std::get<HelperCall>(operation.action);
                        std::swap(call.scopedArguments[0],
                                  call.scopedArguments[1]);
                      }
                      // Specialization has erased static arguments;
                      // preserved source evidence must still agree.
                    }
                    changed = true;
                    break;
                  }
              }
            require(changed, "missing scoped call mapping evidence");
            auto error = specialized ? checkScopedSpecialization(closed)
                                     : checkScopedElaboration(project);
            require(bool(error), "corrupted scoped call mapping accepted");
            require(toString(std::move(error))
                            .find(specialized ? "source.scoped-specialization"
                                              : "source.scoped-witness") !=
                        std::string::npos,
                    "wrong scoped call mapping refusal");
          });
  cases.run("authored witness checks capture operands inside callback", [&] {
    auto project = take(check(captured));
    for (const auto &decl : project.declarations()) {
      if (decl.name != "Demo")
        continue;
      auto body = std::make_shared<Body>(*decl.body);
      const_cast<Declaration &>(decl).body = body;
      auto &binding = body->scopedBindings.front();
      auto computation =
          std::make_shared<ScopedComputation>(*binding.computation);
      auto nested = std::make_shared<Body>(*computation->body);
      binding.computation = computation;
      computation->body = nested;
      auto swap = [](ValueId &v) {
        if (v.index == 1)
          v.index = 2;
        else if (v.index == 2)
          v.index = 1;
      };
      for (auto &op : nested->operations) {
        std::visit(
            [&](auto &action) {
              using T = std::decay_t<decltype(action)>;
              if constexpr (std::is_same_v<T, MathValue> ||
                            std::is_same_v<T, HelperCall> ||
                            std::is_same_v<T, LocalPrimitive>)
                for (auto &v : action.operands)
                  swap(v);
            },
            op.action);
        if (op.binding)
          for (auto &v : op.binding->operands)
            swap(v);
      }
    }
    auto error = checkScopedElaboration(project);
    require(bool(error), "callback capture use mutation accepted");
    require(toString(std::move(error)).find("source.scoped-witness") !=
                std::string::npos,
            "wrong capture use refusal");
  });
  for (unsigned mutation = 0; mutation < 4; ++mutation)
    cases.run(
        "capture occurrence correspondence mutation " +
            std::to_string(mutation),
        [&, mutation] {
          auto project = take(check(R"(
protocol Demo roles(P)(x:Fr@P,a:Fr@P,b:Fr@P)->(r:Fr@P){return forward(x,fn(y)=>{let t=a;y+t-b});}run Run=Demo;
)"));
          bool changed = false;
          for (const auto &decl : project.declarations())
            if (decl.name == "Demo") {
              auto outer = std::make_shared<Body>(*decl.body);
              const_cast<Declaration &>(decl).body = outer;
              auto &binding = outer->scopedBindings.front();
              auto computation =
                  std::make_shared<ScopedComputation>(*binding.computation);
              auto body = std::make_shared<Body>(*computation->body);
              binding.computation = computation;
              computation->body = body;
              if (mutation < 2) {
                for (auto it = body->expressionValues.begin();
                     it != body->expressionValues.end(); ++it)
                  if (it->second.index == 1) {
                    if (mutation == 0)
                      it->second.index = 2;
                    else
                      body->expressionValues.erase(it);
                    changed = true;
                    break;
                  }
              } else {
                for (auto &op : body->operations)
                  if (auto *projection = std::get_if<Projection>(&op.action))
                    if (projection->input.index == 1) {
                      projection->input.index = 2;
                      if (mutation == 3)
                        for (auto &[id, value] : body->expressionValues)
                          if (value.index == 1)
                            value.index = 2;
                      changed = true;
                      break;
                    }
              }
            }
          require(changed, "mutation did not reach a capture read");
          auto error = checkScopedElaboration(project);
          require(bool(error), "corrupted capture occurrence accepted");
          require(toString(std::move(error)).find("source.scoped-witness") !=
                      std::string::npos,
                  "wrong occurrence refusal");
        });
  for (unsigned mutation = 0; mutation < 7; ++mutation)
    cases.run("capture witness mutation " + std::to_string(mutation), [&] {
      auto project = take(check(captured));
      Declaration *declaration = nullptr;
      for (const auto &decl : project.declarations())
        if (decl.name == "Demo")
          declaration = &const_cast<Declaration &>(decl);
      auto body = std::make_shared<Body>(*declaration->body);
      declaration->body = body;
      auto &binding = body->scopedBindings.front();
      auto computation =
          std::make_shared<ScopedComputation>(*binding.computation);
      binding.computation = computation;
      if (mutation == 0)
        std::swap(binding.captures[0], binding.captures[1]);
      if (mutation == 1)
        std::swap(computation->captures[0].binding,
                  computation->captures[1].binding);
      if (mutation == 2)
        computation->captures[0].path.push_back(0);
      if (mutation == 3)
        computation->signature.allowance.mayStop = false;
      if (mutation == 4)
        binding.source.reset();
      if (mutation == 5)
        body->scopedBindings.push_back(binding);
      if (mutation == 6)
        body->scopedBindings.clear();
      auto error = checkScopedElaboration(project);
      require(bool(error), "corrupted capture witness accepted");
      require(toString(std::move(error)).find("source.scoped-witness") !=
                  std::string::npos,
              "wrong capture refusal");
    });
  for (unsigned mutation = 0; mutation < 7; ++mutation)
    cases.run(
        "specialization mapping mutation " + std::to_string(mutation), [&] {
          auto project = take(check(captured));
          auto closed = take(closeEntry(project, "m::Run"));
          Declaration *selected = nullptr;
          for (const auto &decl : closed.declarations())
            if (decl.body &&
                (mutation == 0 || mutation == 5
                     ? decl.kind == Declaration::Kind::Protocol
                 : mutation == 1 ? decl.name == "forward"
                                 : decl.scopedOrigin.has_value())) {
              selected = &const_cast<Declaration &>(decl);
              break;
            }
          require(selected != nullptr, "missing candidate");
          auto body = std::make_shared<Body>(*selected->body);
          selected->body = body;
          if (mutation == 0 || mutation == 1) {
            for (auto &op : body->operations)
              if (auto *call = std::get_if<HelperCall>(&op.action)) {
                if (call->operands.size() >= 3) {
                  std::swap(call->operands[1], call->operands[2]);
                  break;
                }
              }
          }
          if (mutation == 2)
            body->operations.erase(body->operations.begin());
          if (mutation == 3)
            selected->scopedOrigin->second += 1;
          if (mutation == 4)
            selected->inputs.back().type = Type{};
          if (mutation == 5)
            for (auto &op : body->operations)
              if (auto *call = std::get_if<HelperCall>(&op.action))
                call->owner = 99;
          if (mutation == 6)
            body->operations.push_back(body->operations.front());
          auto error = checkScopedSpecialization(closed);
          require(bool(error), "corrupted specialization accepted");
          require(
              toString(std::move(error)).find("source.scoped-specialization") !=
                  std::string::npos,
              "wrong specialization refusal");
        });
  cases.run("captured dependency keeps outer identity across local numbering",
            [] {
              succeeds(R"(
fn invoke(x:Fr,f:fn(Fr)->Fr)->Fr effects(f){return f(x);}
fn adapter(x:Fr,a:fn(Fr)->Fr,b:fn(Fr)->Fr)->Fr effects(b){
 return invoke(x,fn(y)=>invoke(y,fn(z)=>b(z)));
}
fn clean(x:Fr)->Fr effects(){return adapter(x,fn(y)=>{require y==1;y},fn(y)=>y);}
protocol Demo roles(P)(x:Fr@P)->(r:Fr@P){return clean(x);}
run Run=Demo;)");
              refuses(check(R"(
fn invoke(x:Fr,f:fn(Fr)->Fr)->Fr effects(f){return f(x);}
fn adapter(x:Fr,a:fn(Fr)->Fr,b:fn(Fr)->Fr)->Fr effects(a){return invoke(x,fn(y)=>b(y));}
)"),
                      "source.effect");
            });
  cases.run("many forwarding layers preserve precise effects", [] {
    std::string program =
        "fn layer0(x:Fr,f:fn(Fr)->Fr)->Fr effects(f){return f(x);}";
    for (unsigned i = 1; i < 20; ++i)
      program += "fn layer" + std::to_string(i) +
                 "(x:Fr,f:fn(Fr)->Fr)->Fr effects(f){return layer" +
                 std::to_string(i - 1) + "(x,f);}";
    program += "fn clean(x:Fr)->Fr effects(){return layer19(x,fn(y)=>y+1);}";
    succeeds(program);
  });
  for (bool specialized : {false, true})
    cases.run(
        std::string(specialized ? "closed" : "open") +
            " kernel envelope mutation",
        [&] {
          auto project = take(check(R"(
protocol Demo roles(P)(x:Fr@P)->(r:Fr@P){return apply(x,fn(y)=>kernel<Fr>("field.constant";"1"));}
run Run=Demo;)"));
          auto closed = take(closeEntry(project, "m::Run"));
          bool changed = false;
          auto mutate = [&](const std::shared_ptr<const Body> &original) {
            auto body = std::make_shared<Body>(*original);
            for (auto &op : body->operations)
              if (auto *primitive = std::get_if<LocalPrimitive>(&op.action))
                if (primitive->origin == LocalPrimitive::Origin::Kernel) {
                  primitive->origin = LocalPrimitive::Origin::Primitive;
                  body->effects = EffectSummary{};
                  changed = true;
                }
            return body;
          };
          if (specialized) {
            for (const auto &decl : closed.declarations())
              if (decl.scopedOrigin && decl.body)
                const_cast<Declaration &>(decl).body = mutate(decl.body);
          } else {
            for (const auto &decl : project.declarations())
              if (decl.name == "Demo") {
                auto body = std::make_shared<Body>(*decl.body);
                for (auto &binding : body->scopedBindings)
                  if (binding.computation) {
                    auto computation = std::make_shared<ScopedComputation>(
                        *binding.computation);
                    computation->body = mutate(computation->body);
                    binding.computation = computation;
                  }
                const_cast<Declaration &>(decl).body = body;
              }
          }
          require(changed, "kernel mutation not applied");
          auto error = specialized ? checkScopedSpecialization(closed)
                                   : checkScopedElaboration(project);
          require(bool(error), "altered kernel envelope and summary accepted");
          require(toString(std::move(error))
                          .find(specialized ? "source.scoped-specialization"
                                            : "source.scoped-witness") !=
                      std::string::npos,
                  "wrong kernel envelope refusal");
        });
  cases.run("effect transformations enforce shared work limits", [] {
    using namespace zkc::language::detail;
    for (unsigned operation = 0; operation < 4; ++operation) {
      Limits limits;
      limits.work = 0;
      Work work{limits};
      std::vector<Declaration> declarations;
      Semantics types(declarations, {}, work);
      EffectSummary summary;
      summary.dependencies.emplace(0, Effects{true, true});
      EffectSummary into;
      Body body;
      body.mode = Body::Mode::Local;
      bool accepted = operation == 0   ? joinEffects(types, into, summary)
                      : operation == 1 ? effectsWithin(types, summary, summary)
                      : operation == 2
                          ? bool(substituteEffects(types, summary, {summary}))
                          : bool(inferEffects(types, declarations, body));
      require(!accepted && types.diagnostic.has_value(),
              "effect work bypassed limit");
      require(toString(types.takeError()).find("source.limit") !=
                  std::string::npos,
              "wrong effect work refusal");
    }
  });
  cases.run(
      "inspection separates fixed effects from callback dependencies", [] {
        auto project = take(check(R"(
pub fn inspect(x:Fr,a:fn(Fr)->Fr effects(stop),b:fn(Fr)->Fr)->Fr effects(a,b){return a(b(x));}
pub fn selected(x:Fr)->Fr effects(){return inspect(x,fn(y)=>y,fn(y)=>y);}
)"));
        auto value = take(json::parse(take(inspectDeclarations(project))));
        bool found = false;
        for (auto &item : *value.getAsArray()) {
          auto &decl = *item.getAsObject();
          if (decl.getString("kind") == "module")
            continue;
          auto &effects = *decl.getObject("effects");
          require(effects.getBoolean("stop") == false &&
                      effects.getBoolean("opaque") == false,
                  "symbolic maximum leaked into fixed effects");
          auto &dependencies = *effects.getArray("dependencies");
          if (decl.getString("name") == "m::inspect") {
            found = true;
            require(dependencies.size() == 2,
                    "missing inspection dependencies");
            require(
                dependencies[0].getAsObject()->getInteger("callback") == 0 &&
                    dependencies[0].getAsObject()->getBoolean("opaque") ==
                        false &&
                    dependencies[1].getAsObject()->getInteger("callback") ==
                        1 &&
                    dependencies[1].getAsObject()->getBoolean("opaque") == true,
                "inspection lost stable slots or ceilings");
          } else
            require(dependencies.empty(),
                    "selected literal retained dependency");
        }
        require(found, "missing public effect inspection");
      });
  for (unsigned mutation = 0; mutation < 4; ++mutation)
    cases.run(
        "independent symbolic effect mutation " + std::to_string(mutation),
        [&] {
          auto project = take(check(R"(
fn compose(x:Fr,a:fn(Fr)->Fr,b:fn(Fr)->Fr)->Fr{return a(b(x));}
)"));
          for (const auto &decl : project.declarations())
            if (decl.name == "compose") {
              auto body = std::make_shared<Body>(*decl.body);
              if (mutation == 0)
                body->effects.dependencies.erase(0);
              if (mutation == 1)
                body->effects.dependencies[0].opaque = false;
              if (mutation == 2)
                body->effects.dependencies.emplace(100, Effects{true, true});
              if (mutation == 3)
                body->effects.fixed.mayStop = true;
              const_cast<Declaration &>(decl).body = body;
            }
          auto error = checkScopedElaboration(project);
          require(bool(error), "altered open effect summary accepted");
          require(toString(std::move(error)).find("source.scoped-witness") !=
                      std::string::npos,
                  "wrong symbolic summary refusal");
        });
  cases.run("independent closed effect mutation is rejected", [] {
    auto project = take(check(R"(
protocol Demo roles(P)(x:Fr@P)->(r:Fr@P){return forward(x,fn(y)=>y);}
run Run=Demo;)"));
    auto closed = take(closeEntry(project, "m::Run"));
    bool changed = false;
    for (const auto &decl : closed.declarations())
      if (decl.body && decl.name == "forward") {
        auto body = std::make_shared<Body>(*decl.body);
        body->effects.dependencies.emplace(0, Effects{true, true});
        const_cast<Declaration &>(decl).body = body;
        changed = true;
      }
    require(changed, "missing specialized body");
    auto error = checkScopedSpecialization(closed);
    require(bool(error), "open dependency accepted in closed effect summary");
    consumeError(std::move(error));
  });
  return cases.result();
}
