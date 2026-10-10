#include "support/NativeCases.h"
#include "zkc/Language/Inspection.h"
#include "llvm/Support/JSON.h"
#include <set>
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
const std::string prelude = R"(module m;
domain Fr=field("koala-bear");
domain Ext=field("koala-bear.ext8-binomial3");
type Vector<F:Field>=builtin("vector",F);
pub fn sum<F:Field>(xs:Vector<F>)->F=primitive("vector.sum");
math fn square<F:Field>(x:F)->F{return x*x;}
math fn difference<F:Field>(a:F,b:F)->F{return a-b;}
fn custom<F:Field>(xs:Vector<F>)->F{return sum(xs)+1;}
)";
Expected<CheckedProject> check(StringRef text, const Limits &limits = {}) {
  auto captured = capture({{"m", prelude + text.str(), "reductions.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
const Declaration &declaration(const CheckedProject &project, StringRef name) {
  for (const auto &declaration : project.declarations())
    if (declaration.qualifiedName == name)
      return declaration;
  throw std::runtime_error("missing declaration " + name.str());
}
void success(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
void refusal(Error error, StringRef code) {
  require(bool(error), "expected " + code);
  auto message = toString(std::move(error));
  require(message.find(code.str()) != std::string::npos, message);
}
const std::string program = R"(
pub reduction ∑=sum;
pub reduction ∏=sum;
pub fn f<F:Field>(xs:Vector<F>,ys:Vector<F>,a:F,b:F)->F{
  let first=reduce sum [(x,_) in zip(xs,ys)] { b*x+a };
  return first+∑ [(x,y) in zip(xs,ys)] {
    operator *=difference;
    let z=x*y;
    square(z)+a
  };
}
protocol Demo roles(P)(xs:Vector<Fr>@P,ys:Vector<Fr>@P,a:Fr@P,b:Fr@P)->(r:Fr@P){
  return (r=f(xs,ys,a,b));
}
run Run=Demo;
)";
} // namespace
int main() {
  Cases cases;
  cases.run("named and symbolic generic reductions retain scoped helpers", [] {
    auto project = take(check(program));
    success(checkReductionElaboration(project));
    auto closed = take(closeEntry(project, "m::Run"));
    (void)closed;
    unsigned generated = 0;
    for (const auto &decl : project.declarations())
      if (decl.generatedReduction) {
        ++generated;
        require(decl.parameters.size() == 1 &&
                    decl.symbol.rfind("zki_", 0) == 0 && decl.anonymous &&
                    !decl.isPublic,
                "helper identity or generic context lost");
        for (unsigned i = 0; i < decl.body->inputs; ++i)
          require(decl.body->values[i].components == std::vector<unsigned>{i},
                  "math dependency uses local ownership");
      }
    require(generated == 2, "generated helper count differs");
    auto declarationReport = take(inspectDeclarations(project));
    require(declarationReport.find("reduction<") == std::string::npos,
            "private helper leaked");
    auto notationReport = take(inspectNotations(project, {true, false}));
    auto report = take(json::parse(notationReport));
    require(report.getAsObject() != nullptr &&
                notationReport.find("reduction") != std::string::npos,
            "notation inspection lost reduction descriptors");
  });
  for (const auto &body :
       {"reduce sum [x in xs] {x*x}", "reduce custom [x in xs] {x}",
        "reduce sum<Fr> [_ in xs] {1}", "reduce sum [(x,_) in zip(xs,xs)] {x}",
        "reduce sum [a in xs] {let t=a; t+a}",
        "reduce sum [x in xs] {({let x=a; x})+x}",
        "reduce sum [x in xs] {intrinsic<Fr>(\"field.mul\",x,a)}"})
    cases.run(body, [&] {
      take(check("fn f(xs:Vector<Fr>,a:Fr)->Fr{return " + std::string(body) +
                 ";}"));
    });
  cases.run("symbolic product spelling may select an ordinary custom reducer",
            [] {
              take(check("reduction ∏=custom;fn f(xs:Vector<Fr>)->Fr{return ∏ "
                         "[x in xs]{x};}"));
            });
  cases.run("local reduction family overrides without fallback", [] {
    auto project =
        take(check("reduction ∑=sum;fn f(xs:Vector<Fr>)->Fr{reduction "
                   "∑=custom;return ∑ [x in xs]{x};}"));
    const auto &op = declaration(project, "m::f").body->operations.back();
    require(op.binding && op.binding->target.declaration.index ==
                              declaration(project, "m::custom").id.index,
            "local reducer lost");
  });
  cases.run("selective import and reexport retain reduction identity", [] {
    auto project = take(capture(
        {{"lib",
          R"(module lib;pub type Vector<F:Field>=builtin("vector",F);pub fn sum<F:Field>(xs:Vector<F>)->F=primitive("vector.sum");pub reduction ∑=sum;)",
          {}},
         {"bridge", "module bridge;pub use lib::{Vector,sum,reduction ∑};", {}},
         {"m",
          R"(module m;use bridge::{Vector,reduction ∑};domain F=field("koala-bear");fn f(xs:Vector<F>)->F{return ∑ [x in xs]{x};})",
          {}}}));
    take(analyze(project).checkedProject());
  });
  for (bool alias : {false, true})
    cases.run(
        alias ? "module alias activates reductions"
              : "named imports do not activate reductions",
        [&] {
          auto project = take(capture(
              {{"lib",
                R"(module lib;pub type Vector<F:Field>=builtin("vector",F);pub fn sum<F:Field>(xs:Vector<F>)->F=primitive("vector.sum");pub reduction ∑=sum;)",
                {}},
               {"m",
                std::string("module m;") +
                    (alias
                         ? "use lib as lib;type Vector<T:Field>=lib::Vector<T>;"
                         : "use lib::{Vector,sum};") +
                    R"(domain F=field("koala-bear");fn f(xs:Vector<F>)->F{return ∑ [x in xs]{x};})",
                {}}}));
          auto result = analyze(project).checkedProject();
          if (alias)
            take(std::move(result));
          else
            refuses(std::move(result), "source.notation-visibility");
        });
  const std::vector<std::pair<std::string, std::string>> bad = {
      {"reduction ⊕=sum;", "source.reduction"},
      {"reduction ∑=square;", "source.reduction-target"},
      {"fn f(xs:Vector<Fr>)->Fr{return reduce square[x in xs]{x};}",
       "source.type"},
      {"reduction ∑=sum;reduction ∑=custom;fn f(xs:Vector<Fr>)->Fr{return ∑[x "
       "in xs]{x};}",
       "source.operator"},
      {"fn f(xs:Vector<Fr>)->Fr{return reduce sum[(x,x) in zip(xs,xs)]{x};}",
       "source.binding"},
      {"fn f(xs:Vector<Fr>)->Fr{return reduce sum[(x,y) in xs]{x};}",
       "source.syntax"},
      {"fn f(xs:Vector<Fr>)->Fr{return reduce sum[x in zip(xs,xs)]{x};}",
       "source.reduction"},
      {"fn f(xs:Vector<Fr>)->Fr{return reduce sum[(x,y) in zip(xs)]{x};}",
       "source.reduction"},
      {"fn f(xs:Vector<Fr>)->Fr{return reduce sum[(x) in zip(xs)]{x};}",
       "source.reduction"},
      {"fn f(xs:Vector<Fr>)->Fr{return reduce sum[x in xs,y in xs]{x};}",
       "source.syntax"},
      {"fn f(xs:Vector<Fr>)->Fr{return reduce sum[x in x]{x};}", "source.name"},
      {"fn f(xs:Vector<Fr>)->Fr{let r=reduce sum[x in xs]{x};return x;}",
       "source.name"},
      {"fn f(xs:Vector<Fr>)->Fr{return reduce sum[x in xs]{reduce sum[y in "
       "xs]{y}};}",
       "source.reduction"},
      {"math fn f(xs:Vector<Fr>)->Fr{return reduce sum[x in xs]{x};}",
       "source.mode"},
      {"fn f(xs:Vector<Fr>,a:Fr)->Fr{let mut b=a;return reduce sum[x in "
       "xs]{b*x};}",
       "source.reduction-capture"},
      {"fn f(xs:Vector<Fr>,a:Fr)->Fr{let mut x=a;return reduce sum[x in "
       "xs]{x};}",
       "source.shadow"},
      {"fn f(xs:Vector<Fr>)->Fr{return reduce sum[x in xs]{let mut y=x;y};}",
       "source.reduction-body"},
      {"fn f(xs:Vector<Fr>)->Fr{return reduce sum[x in "
       "xs]{kernel<Fr>(\"field.inverse\",x)};}",
       "source.reduction-body"},
      {"fn effect(x:Fr)->Fr{return x;}fn f(xs:Vector<Fr>)->Fr{return reduce "
       "sum[x in xs]{effect(x)};}",
       "source.mode"},
      {"fn f(xs:Vector<Fr>,a:Ext)->Fr{return reduce sum[x in xs]{a};}",
       "source.type"},
      {"fn f(xs:Vector<Fr>,a:(Fr,Fr))->Fr{return reduce sum[x in xs]{a.0};}",
       "source.reduction-body"},
      {"fn f(xs:[Fr;2])->Fr{return reduce sum[x in xs]{x};}", "source.type"},
      {"fn f(xs:Vector<Fr>,ys:Vector<Ext>)->Fr{return reduce sum[(x,y) in "
       "zip(xs,ys)]{x};}",
       "source.type"},
      {"math fn bad(x:Fr)->Fr{let ignored=x==x;return x;}fn "
       "f(xs:Vector<Fr>)->Fr{return reduce sum[x in xs]{bad(x)};}",
       "source.reduction-body"},
      {"fn f(xs:Vector<Fr>)->Fr{return reduce sum[x in xs]{let "
       "ignored=x==x;x};}",
       "source.reduction-body"},
  };
  for (const auto &test : bad)
    cases.run(test.first, [&] { refuses(check(test.first), test.second); });
  cases.run(
      "capture order follows first textual use and ignores unused rows", [] {
        auto project =
            take(check("fn f(xs:Vector<Fr>,ys:Vector<Fr>,a:Fr,b:Fr)->Fr{return "
                       "reduce sum[(_,x) in zip(xs,ys)]{b*x+a+b};}"));
        const auto &body = *declaration(project, "m::f").body;
        require(body.operations.size() == 4,
                "expected two capture reads then map and reducer");
        require(
            std::get<Projection>(body.operations[0].action).input.index == 3 &&
                std::get<Projection>(body.operations[1].action).input.index ==
                    2,
            "captures were sorted by declaration instead of use");
        auto &map = std::get<BulkApplication>(body.operations[2].action);
        require(map.mapped == std::vector<bool>({true, true, false, false}),
                "strict mask dropped ignored input");
      });
  for (unsigned limit = 1; limit <= 5; ++limit)
    cases.run("exact generated helper depth " + Twine(limit), [&] {
      Limits limits;
      limits.callDepth = limit;
      auto project = check(
          "fn f(xs:Vector<Fr>)->Fr{return reduce sum[x in "
          "xs]{square(x)};}protocol Demo "
          "roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return(r=f(xs));}run Run=Demo;",
          limits);
      if (limit < 4)
        refuses(std::move(project), "source.limit");
      else {
        auto checked = take(std::move(project));
        take(closeEntry(checked, "m::Run", limits));
      }
    });
  cases.run("constant helper adds a depth edge even without calls", [] {
    Limits limits;
    limits.callDepth = 2;
    refuses(
        check("fn f(xs:Vector<Fr>)->Fr{return reduce sum[_ in xs]{1};}protocol "
              "Demo roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return(r=f(xs));}run "
              "Run=Demo;",
              limits),
        "source.limit");
    limits.callDepth = 3;
    auto project = take(check(
        "fn f(xs:Vector<Fr>)->Fr{return reduce sum[_ in xs]{1};}protocol Demo "
        "roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return(r=f(xs));}run Run=Demo;",
        limits));
    take(closeEntry(project, "m::Run", limits));
  });
  cases.run("declaration, operation and work budgets include generated work",
            [] {
              auto project = take(check(program));
              Limits limits;
              limits.declarations = project.checkedDeclarations() - 1;
              refuses(check(program, limits), "source.limit");
              limits = {};
              limits.operations = project.checkedOperations() - 1;
              refuses(check(program, limits), "source.limit");
              limits = {};
              limits.work = project.checkedWork() - 1;
              refuses(check(program, limits), "source.limit");
            });
  const std::vector<std::string> mutations = {
      "capture",     "capture-order",  "mask",         "row",
      "field",       "reducer",        "map-origin",   "capture-origin",
      "body-origin", "input-binding",  "body-operand", "missing-evidence",
      "helper-name", "helper-display", "helper-parent"};
  for (const auto &mutation : mutations)
    cases.run("independent extraction rejects " + mutation, [&] {
      auto project =
          take(check("fn f(xs:Vector<Fr>,ys:Vector<Fr>,a:Fr,b:Fr)->Fr{return "
                     "reduce sum[(x,y) in zip(xs,ys)]{b*x+a*y};}"));
      auto &function = const_cast<Declaration &>(declaration(project, "m::f"));
      auto changed = std::make_shared<Body>(*function.body);
      function.body = changed;
      auto &op = changed->operations[2];
      auto &bulk = std::get<BulkApplication>(op.action);
      auto &helper =
          const_cast<Declaration &>(project.declarations()[bulk.callee.index]);
      if (mutation == "capture")
        bulk.operands[2] = bulk.operands[3];
      if (mutation == "capture-order")
        std::swap(bulk.operands[2], bulk.operands[3]);
      if (mutation == "mask")
        bulk.mapped[1] = false;
      if (mutation == "row")
        std::swap(bulk.operands[0], bulk.operands[1]);
      if (mutation == "field")
        helper.outputs[0].type = Type{};
      if (mutation == "reducer")
        changed->operations[3].binding->target.declaration =
            declaration(project, "m::custom").id;
      if (mutation == "map-origin")
        ++op.span.begin;
      if (mutation == "capture-origin")
        ++changed->operations[0].span.begin;
      if (mutation == "body-origin" || mutation == "body-operand") {
        auto scalar = std::make_shared<Body>(*helper.body);
        helper.body = scalar;
        if (mutation == "body-origin")
          ++scalar->operations[0].span.begin;
        else
          std::get<MathValue>(scalar->operations[0].action).operands[0] = {0};
      }
      if (mutation == "input-binding")
        std::swap(op.reduction->inputs[2], op.reduction->inputs[3]);
      if (mutation == "missing-evidence")
        op.reduction.reset();
      if (mutation == "helper-name")
        helper.symbol = "zki_invalid";
      if (mutation == "helper-display")
        helper.qualifiedName = "m::f::wrong";
      if (mutation == "helper-parent")
        helper.parent.reset();
      refusal(checkReductionElaboration(project),
              mutation == "body-operand" ? "source.binding-witness"
                                         : "source.reduction-witness");
    });
  cases.run("inspection owns extracted operation pointers after analysis dies",
            [] {
              auto project = take(check(program));
              std::vector<std::string> churn(2000, std::string(1024, 'x'));
              (void)churn;
              auto first = take(inspectNotations(project, {true, false}));
              auto second = take(inspectNotations(project, {true, false}));
              require(first == second,
                      "inspection depends on expired analysis storage");
              require(first.find("not-emitted") == std::string::npos,
                      "generated notation was lost");
            });

  cases.run("local prefix and forward notation keep their authored scopes", [] {
    auto project = take(check(R"(
      operator prefix(75) ⊖=square;
      fn f(xs:Vector<Fr>)->Fr {
        return reduce sum[x in xs]{
          operator ⊗=difference;
          operator infixl(70) ⊗=difference;
          operator prefix(75) ⊖=identity;
          ⊖x ⊗ x
        };
      }
      math fn identity(x:Fr)->Fr{return x;}
    )"));
    success(checkReductionElaboration(project));
    for (const auto &decl : project.declarations())
      if (decl.generatedReduction) {
        const auto &first = decl.body->operations.front();
        require(first.binding &&
                    first.binding->target.declaration.index ==
                        declaration(project, "m::identity").id.index,
                "prefix was resolved outside its authored scope");
      }
  });
  cases.run(
      "collections are evaluated once in written order before captures", [] {
        auto project = take(check(R"(
      fn first(xs:Vector<Fr>)->Vector<Fr>{return xs;}
      fn second(xs:Vector<Fr>)->Vector<Fr>{return xs;}
      fn f(xs:Vector<Fr>,a:Fr)->Fr {
        return reduce sum[(x,y,z) in zip(second(xs),first(xs),second(xs))]{x*y*z+a};
      }
    )"));
        const auto &body = *declaration(project, "m::f").body;
        require(body.operations.size() == 6,
                "collection was evaluated more than once");
        const std::vector<std::string> targets = {"m::second", "m::first",
                                                  "m::second"};
        for (unsigned i = 0; i < targets.size(); ++i)
          require(body.operations[i].binding &&
                      body.operations[i].binding->target.declaration.index ==
                          declaration(project, targets[i]).id.index,
                  "collection evaluation order changed");
        require(std::holds_alternative<Projection>(body.operations[3].action),
                "capture read preceded collections");
        success(checkReductionElaboration(project));
      });
  cases.run("abstract same-field math dispatch is outside the ring profile",
            [] {
              refuses(check(R"(
      interface Step<F:Field>{math fn apply(x:F)->F;}
      fn f<C:Step<Fr>>(xs:Vector<Fr>)->Fr{return reduce sum[x in xs]{C::apply(x)};}
    )"),
                      "source.reduction-body");
            });
  cases.run("component members require a separate self-capture contract", [] {
    refuses(check(R"(
      interface Step<F:Field>{fn apply(xs:Vector<F>)->F;}
      component Impl<F:Field>:Step<F>{
        fn apply(xs:Vector<F>)->F{return reduce sum[x in xs]{x};}
      }
    )"),
            "source.reduction-body");
  });
  cases.run("reducer signatures must preserve the vector field exactly", [] {
    refuses(check(R"(
      fn wrong(xs:Vector<Fr>)->Ext{stop "wrong field";}
      reduction ∑=wrong;
    )"),
            "source.reduction-target");
  });
  cases.run("generated helpers are not source-resolvable members", [] {
    refuses(check(R"(
      fn f(xs:Vector<Fr>)->Fr{return reduce sum[x in xs]{x};}
      fn g(x:Fr)->Fr{return f::reduction(x);}
    )"),
            "source.name");
  });
  for (bool helper : {false, true})
    cases.run(helper ? "deferred helper notation charges its extra edge"
                     : "deferred inline notation uses Math depth",
              [&] {
                auto source =
                    std::string(helper ? "operator prefix(75) ⊖=square;" : "") +
                    "fn f(xs:Vector<Fr>)->Fr{return reduce sum[x in xs]{" +
                    (helper ? "⊖x" : "x+x") +
                    "};}"
                    "protocol Demo "
                    "roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return(r=f(xs));}run "
                    "Run=Demo;";
                Limits limits;
                limits.callDepth = helper ? 4 : 3;
                auto checked = take(check(source, limits));
                take(closeEntry(checked, "m::Run", limits));
                --limits.callDepth;
                refuses(check(source, limits), "source.limit");
                refuses(closeEntry(checked, "m::Run", limits), "source.limit");
              });
  cases.run("many pending helpers retain stable distinct site identities", [] {
    std::string source = "fn f(xs:Vector<Fr>)->Fr{";
    for (unsigned i = 0; i < 64; ++i)
      source += "let r" + std::to_string(i) + "=reduce sum[x in xs]{x+1};";
    source += "return r63;}";
    auto first = take(check(source));
    auto second = take(check(source));
    std::set<std::string> symbols;
    unsigned ordinal = 0;
    for (const auto &decl : first.declarations())
      if (decl.generatedReduction) {
        require(decl.generatedReduction->ordinal == ++ordinal,
                "site preorder changed");
        require(symbols.insert(decl.symbol).second,
                "generated identity collided");
        require(decl.symbol == second.declarations()[decl.id.index].symbol,
                "generated identity is unstable");
      }
    require(ordinal == 64, "pending helper was lost");
    success(checkReductionElaboration(first));
    auto report = take(inspectNotations(first, {true, false}));
    require(report.find("not-emitted") == std::string::npos,
            "pending helper lost notation evidence");
  });
  cases.run("closure independently rejects altered extraction evidence", [] {
    auto project = take(check(program));
    auto &function = const_cast<Declaration &>(declaration(project, "m::f"));
    auto changed = std::make_shared<Body>(*function.body);
    function.body = changed;
    for (auto &op : changed->operations)
      if (op.reduction) {
        std::get<BulkApplication>(op.action).mapped[1] = false;
        break;
      }
    refuses(closeEntry(project, "m::Run"), "source.reduction-witness");
  });

  cases.run("helpers inherit requirements completed after the binder", [] {
    auto project = take(check(R"(
      fn root<F:Field>(n:index)->F where zkc::algebra::TwoAdicField(F) {
        return kernel<F>("poly.domain_root",n);
      }
      fn f<F:Field>(xs:Vector<F>,n:index)->F{
        let r=reduce sum[x in xs]{x*x};
        return r+root<F>(n);
      }
      protocol Demo roles(P)(xs:Vector<Fr>@P,n:index@P)->(r:Fr@P){return(r=f(xs,n));}
      run Run=Demo;
    )"));
    const auto &owner = declaration(project, "m::f");
    require(!owner.capabilityBounds.empty(), "expected an inferred capability");
    for (const auto &decl : project.declarations())
      if (decl.generatedReduction) {
        require(decl.capabilityBounds.size() == owner.capabilityBounds.size(),
                "helper inherited an incomplete contract");
        for (unsigned i = 0; i < owner.capabilityBounds.size(); ++i)
          require(decl.capabilityBounds[i].predicate ==
                          owner.capabilityBounds[i].predicate &&
                      decl.capabilityBounds[i].arguments ==
                          owner.capabilityBounds[i].arguments,
                  "helper requirement differs from completed owner");
      }
    take(closeEntry(project, "m::Run"));
  });
  cases.run("mutable capture assigned by a collection remains inadmissible",
            [] {
              refuses(check(R"(
      fn f(xs:Vector<Fr>,a:Fr)->Fr{
        let mut b=a;
        return reduce sum[x in {b=b+1;xs}]{x+b};
      }
    )"),
                      "source.reduction-capture");
            });
  return cases.result();
}
