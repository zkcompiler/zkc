#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Language/Inspection.h"
#include "llvm/Support/JSON.h"
using namespace llvm;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
Expected<CheckedProject> check(std::vector<SourceBuffer> sources,
                               const Limits &limits = {}) {
  auto input = capture(std::move(sources));
  if (!input)
    return input.takeError();
  return analyze(*input, limits).checkedProject();
}
Expected<CheckedProject> check(StringRef text, const Limits &limits = {}) {
  return check({SourceBuffer{"m", "module m;" + text.str(), {}}}, limits);
}
const Declaration &decl(const CheckedProject &project, StringRef name) {
  for (const auto &value : project.declarations())
    if (value.qualifiedName == name)
      return value;
  throw std::runtime_error("missing declaration: " + name.str());
}
std::string localAction(const Declaration &value) {
  return std::get<LocalPrimitive>(value.body->operations.back().action)
      .contract;
}
} // namespace
int main() {
  zkc::test::Cases cases;
  const std::string field = "domain F=field(\"bls12-381.fr\");";
  const std::string vector = R"(module v;
    pub type Vector<F:Field> = builtin("vector",F);
    pub fn add<F:Field>(a:Vector<F>, b:Vector<F>)->Vector<F> = primitive("vector.add");
    pub operator + = add;
  )";
  cases.run("prelude is installed separately from capture", [&] {
    auto captureValue = take(capture({{"m", "module m;", {}}}));
    auto project = take(analyze(captureValue).checkedProject());
    require(project.capture().identity() == captureValue.identity() &&
                project.capture().sources().size() == 1,
            "prelude altered capture identity or files");
    require(project.sources().size() == 2 &&
                project.sources().back().origin == SourceOrigin::Installation,
            "prelude source origin is missing");
    refuses(capture({{"zkc::prelude", "module zkc::prelude;", {}}}),
            "source.module");
    Limits limits;
    limits.files = 1;
    take(analyze(captureValue, limits).checkedProject());
  });
  cases.run("inspection distinguishes public primitive definitions", [&] {
    auto project = take(
        check(field + "pub math fn add(a:F,b:F)->F=primitive(\"field.add\");"));
    auto report = take(llvm::json::parse(take(inspectDeclarations(project))));
    auto *items = report.getAsArray();
    require(items && items->size() == 1,
            "installation declarations leaked into captured inventory");
    auto *item = items->front().getAsObject();
    require(item && item->getString("definition") == "primitive" &&
                item->getString("primitive") == "field.add" &&
                item->getObject("source")->getString("origin") == "captured",
            "primitive identity or source origin is missing");
  });
  cases.run("named and operator scalar calls emit direct primitives", [&] {
    auto project = take(check(field + R"(
      fn named(a:F,b:F)->F {return zkc::prelude::field_add(a,b);}
      fn infix(a:F,b:F)->F {return a+b;}
      math fn total(a:F,b:F)->F {return a+b;}
      fn index_sum(a:index,b:index)->index{return a+b;}
      fn index_eq(a:index,b:index)->bool{return a==b;}
    )"));
    require(localAction(decl(project, "m::named")) == "field.add" &&
                localAction(decl(project, "m::infix")) == "field.add",
            "scalar call acquired a wrapper");
    require(!decl(project, "m::named").body->mayStop &&
                !decl(project, "m::total").body->mayStop,
            "total scalar primitive became stopping");
    require(decl(project, "m::index_sum").body->mayStop &&
                !decl(project, "m::index_eq").body->mayStop,
            "index primitive effects changed");
    require(std::get<MathValue>(
                decl(project, "m::total").body->operations.back().action)
                    .identity == zkc::MathematicalIdentity::FieldAdd,
            "math identity changed");
  });
  for (StringRef import :
       {"use v;", "use v as vec;", "use v::{Vector,operator +};"})
    cases.run("operator activation: " + import, [&] {
      auto project = take(check(
          {{"v", vector, {}},
           {"m",
            "module m;" + import.str() + field +
                "fn f(a:v::Vector<F>,b:v::Vector<F>)->v::Vector<F>{return "
                "a+b;}",
            {}}}));
      require(localAction(decl(project, "m::f")) == "vector.add",
              "vector lost native identity");
      require(decl(project, "m::f").body->mayStop,
              "vector shape failure erased");
    });
  cases.run("named-only import leaves operators inactive", [&] {
    refuses(check({{"v", vector, {}},
                   {"m",
                    "module m;use v::{Vector,add};" + field +
                        "fn f(a:Vector<F>,b:Vector<F>)->Vector<F>{return a+b;}",
                    {}}}),
            "source.operator");
    take(check({{"v", vector, {}},
                {"m",
                 "module m;" + field +
                     "fn f(a:v::Vector<F>,b:v::Vector<F>)->v::Vector<F>{return "
                     "v::add(a,b);}",
                 {}}}));
  });
  cases.run("public reexports retain identity", [&] {
    take(check(
        {{"v", vector, {}},
         {"r", "module r;pub use v::{Vector,add,operator +};", {}},
         {"m",
          "module m;use r;use v;" + field +
              "fn f(a:r::Vector<F>,b:r::Vector<F>)->r::Vector<F>{return a+b;}",
          {}}}));
  });
  cases.run("local replacement has no type-directed fallback", [&] {
    refuses(check(field + R"(
      fn weird(a:bool,b:bool)->bool{return a;}
      fn f(a:F,b:F)->F {operator + = weird;return a+b;}
    )"),
            "source.operator");
  });
  cases.run("result context cannot choose equal input meanings", [&] {
    refuses(check(field + R"(
      math fn first(a:F,b:F)->F{return a;}
      math fn second(a:F,b:F)->bool{return true;}
      fn f(a:F,b:F)->F {operator + = first;operator + = second;return a+b;}
    )"),
            "source.operator");
  });
  cases.run("fixed negation ignores overloaded equality", [&] {
    auto project = take(check(R"(
      fn equal(a:bool,b:bool)->bool{return false;}
      fn f(a:bool)->bool{operator == = equal;return !a;}
    )"));
    require(localAction(decl(project, "m::f")) == "bool.equal",
            "negation used overloaded equality");
  });
  cases.run("nested statement cannot finalize enclosing operator early", [&] {
    take(check(field + "fn f(a:F)->F{return (0+0)+{let b:bool=true;a};}"));
    refuses(check(field + "fn f(a:F)->F{return {let b=0+0;a};}"),
            "source.inference");
  });
  cases.run("rejected projection branch preserves place diagnostics", [&] {
    refuses(check(field + R"(
      fn first<N:nat>(a:F,b:index)->[bool;N]{stop "reject";}
      fn second(a:F,b:F)->[F;8]{stop "reject";}
      fn f<K:nat>(a:F,x:[F;K])->F{
        operator + = first<N=K>;
        operator + = second;
        let v:F=(a+1)[3];
        return v;
      }
    )"),
            "source.place");
  });
  cases.run("projection bounds do not break overload ties", [&] {
    refuses(check(field + R"(
      fn first<N:nat>(a:F,b:index)->[F;N]{stop "reject";}
      fn second(a:F,b:F)->[F;8]{stop "reject";}
      fn f<K:nat>(a:F,x:[F;K])->F where K <= K {
        operator + = first<N=K>;
        operator + = second;
        return (a+1)[3];
      }
    )"),
            "source.operator");
  });
  cases.run(
      "primitive roots come from ports rather than generic position", [&] {
        auto project = take(check(field + R"(
      math fn add<G:Group,T:Field>(a:T,b:T)->T=primitive("field.add");
      math fn closed(a:F,b:F)->F=primitive("field.add");
    )"));
        require(decl(project, "m::add").primitive->arguments.front().domain ==
                    decl(project, "m::add").parameters[1].atom,
                "extra or reordered generic parameter became a primitive root");
      });
  for (const auto &[source, code] :
       std::vector<std::pair<std::string, std::string>>{
           {"math fn f(a:F,b:F)->bool=primitive(\"field.add\");",
            "source.primitive"},
           {"fn f(a:F,b:F)->F=primitive(\"field.add\");", "source.primitive"},
           {"math fn f(a:F,b:F)->F=primitive(\"unknown.operation\");",
            "source.primitive"},
           {"operator + = f;fn f(a:F,b:F){return a;}", "source.operator"},
           {"operator == = f;fn f(a:F,b:F)->F{return a;}", "source.operator"},
           {"fn f(a:F,b:F)->F{let x=a;operator + = f;return a;}",
            "source.operator"}})
    cases.run("invalid operator or primitive: " + source,
              [&, source = source, code = code] {
                refuses(check(field + source), code);
              });
  cases.run("operator-selected recursion is refused", [&] {
    refuses(check(field + "fn f(a:F,b:F)->F{operator + = f;return a+b;}"),
            "source.cycle");
  });
  cases.run("primitive input names follow ordinary lexical rules", [&] {
    refuses(check(field + "math fn bad(a:F,a:F)->F=primitive(\"field.add\");"),
            "source.duplicate");
    refuses(check(field + "math fn bad(F:F,b:F)->F=primitive(\"field.add\");"),
            "source.shadow");
  });
  cases.run("explicit component operators retain their definition binding",
            [&] {
              take(check(R"(
      interface Arithmetic<T:Type+Copy+Drop>{math fn add(a:T,b:T)->T;}
      math fn sum<T:Type+Copy+Drop,A:Arithmetic<T>>(a:T,b:T)->T {
        operator + = A::add;
        return a+b;
      }
    )"));
            });
  cases.run(
      "many constrained scalar statements fit the normal work budget", [&] {
        std::string source = field + "fn many(x:F)->F{";
        for (unsigned i = 0; i < 256; ++i)
          source += "let v" + std::to_string(i) + " = (x+1)*(x+2)+(x+3)*(x+4);";
        source += "return v255;}";
        auto project = take(check(source));
        llvm::outs() << "operator stress work: " << project.checkedWork()
                     << " / " << Limits{}.work << "\n";
      });
  cases.run(
      "operator imports are independent of capture and import ordering", [&] {
        for (bool reverse : {false, true}) {
          std::vector<SourceBuffer> sources{
              {"v", vector, {}},
              {"r",
               "module r;pub use v as vectors;pub use v::{operator +};",
               {}},
              {"m",
               "module m;" +
                   std::string(reverse ? "use r;use v;" : "use v;use r;") +
                   field +
                   "fn "
                   "sum(a:r::vectors::Vector<F>,b:v::Vector<F>)->v::Vector<F>{"
                   "return a+b;}",
               {}}};
          if (reverse)
            std::reverse(sources.begin(), sources.end());
          auto project = take(check(std::move(sources)));
          require(localAction(decl(project, "m::sum")) == "vector.add",
                  "import ordering changed operator selection");
        }
      });
  cases.run("private imports do not reexport operators", [&] {
    refuses(
        check(
            {{"v", vector, {}},
             {"r", "module r;use v;", {}},
             {"m",
              "module m;use r;" + field +
                  "fn sum(a:v::Vector<F>,b:v::Vector<F>)->v::Vector<F>{return "
                  "a+b;}",
              {}}}),
        "source.operator");
  });
  cases.run("module aliases share the lexical namespace", [&] {
    refuses(check({{"v", vector, {}},
                   {"m", "module m;use v as Values;type Values=bool;", {}}}),
            "source.duplicate");
    refuses(check({{"v", vector, {}},
                   {"m", "module m;use v;fn f(v:bool)->bool{return v;}", {}}}),
            "source.shadow");
  });
  cases.run("effects and body modes cannot select an overload", [&] {
    refuses(check(field + R"(
      math fn total(a:F,b:F)->F{return a;}
      fn stopping(a:F,b:F)->F{stop "reject";}
      math fn f(a:F,b:F)->F{operator + = total;operator + = stopping;return a+b;}
    )"),
            "source.operator");
  });
  cases.run("definition component binding survives entry specialization", [&] {
    auto project = take(check(field + R"(
      interface Arithmetic<T:Field>{math fn add(a:T,b:T)->T;}
      component Ordinary<T:Field>:Arithmetic<T>{
        math fn add(a:T,b:T)->T{return a+b;}
      }
      math fn sum<T:Field,A:Arithmetic<T>>(a:T,b:T)->T{
        operator + = A::add;return a+b;
      }
      math fn other(a:F,b:F)->F{return a-b;}
      protocol Run roles(P)(x:F@P)->(out:F@P){
        operator + = other;
        return sum<T=F,A=Ordinary<F>>(x,x);
      }
      run Demo=Run;
    )"));
    take(prepareOriginal(take(closeEntry(project, "m::Demo"))));
  });
  cases.run("contextual notation words remain ordinary identifiers", [&] {
    take(check(
        "fn primitive(operator:bool,as:bool)->bool{return operator==as;}"));
  });
  cases.run("unavailable representations do not select operators", [&] {
    refuses(check(field + R"(
      interface I{type T:Copy+Drop;}
      struct Pair{pub first:F,pub second:bool}
      fn unknown<A:I>(a:F,b:index)->A::T{stop "reject";}
      fn known(a:F,b:F)->Pair{return Pair{first:a,second:true};}
      fn f<A:I>(a:F)->(F,bool){
        operator + = unknown<A>;operator + = known;
        return unpack(a+1);
      }
    )"),
            "source.operator");
  });
  cases.run("negation uses the reserved absolute prelude identity", [&] {
    auto project = take(
        check("fn zkc()->bool{return true;}fn f(a:bool)->bool{return !a;}"));
    require(localAction(decl(project, "m::f")) == "bool.equal",
            "local declaration captured negation");
    project =
        take(check({{"helpers",
                     "module helpers;pub math fn "
                     "boolean_equal(a:bool,b:bool)->bool{return false;}",
                     {}},
                    {"other", "module other;pub use helpers as prelude;", {}},
                    {"m",
                     "module m;use other as zkc;fn f(a:bool)->bool{return !a;}",
                     {}}}));
    require(localAction(decl(project, "m::f")) == "bool.equal",
            "module alias captured negation");
  });
  cases.run("witness and inference exclude overflowing natural competitors",
            [&] {
              take(check(field + R"(
      fn table<N:nat>(a:[F;N],b:[F;pow2(N)])->F{stop "reject";}
      fn pick(a:[F;64],b:[F;1])->F{stop "reject";}
      fn f(a:[F;64],b:[F;1])->F{
        operator + = table;operator + = pick;return a+b;
      }
    )"));
            });
  cases.run("match receives operator signature constraints through named calls",
            [&] {
              take(check(field + R"(
      enum Option<T:Type>{Some(T),None()}
      fn wrap<T:Type>(v:T)->Option<T>{return Option::Some<T>(v);}
      fn f(x:F,y:F)->F{return match wrap(x+y){Some(v)=>{v},None()=>{0}};}
      fn choose(a:F,b:F)->Option<F>{return wrap(a+b);}
      fn g(x:F,y:F)->F{operator + = choose;
        return match x+y{Some(v)=>{v},None()=>{0}};}
      fn nested(x:F,y:F)->F{
        return (0+0)+match wrap(x+y){Some(v)=>{v},None()=>{0}};
      }
    )"));
            });
  cases.run("unique signature preserves invalid field diagnostics", [&] {
    refuses(check(field + R"(
      struct Pair {pub x:F,pub y:F}
      fn pair(a:F,b:F)->Pair{return Pair{x:a,y:b};}
      fn f(a:F,b:F)->F{operator + = pair;return (a+b).missing;}
    )"),
            "source.field");
  });
  cases.run(
      "unresolved named statics retain their explanation beside operators",
      [&] {
        auto result = check(field + R"(
      fn unconstrained<N:nat>(x:F)->F{return x;}
      fn f(x:F)->F{return unconstrained(x)+x;}
    )");
        require(!result, "unconstrained static was accepted");
        auto message = llvm::toString(result.takeError());
        require(message.find(
                    "cannot infer static argument 'N' of m::unconstrained") !=
                    std::string::npos,
                "operator resolution hid the unknown named static: " + message);
      });
  return cases.result();
}
