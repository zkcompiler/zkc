#include "support/NativeCases.h"
#include "zkc/Language/Inspection.h"
#include "llvm/Support/JSON.h"
#include <set>
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
const std::string definitions = R"(
pub type Vector<F:Field>=builtin("vector",F);
pub domain fn zip<A:Type+Copy+Drop,B:Type+Copy+Drop>(a:scoped domain<A>,b:scoped domain<B>)->scoped domain<(A,B)>=domain("zip");
pub fn fold<I:Type+Copy+Drop,S:Type>(rows:scoped domain<I>,initial:S,step:scoped fn(S,I)->S !{stop} on(rows))->S !{stop}=finite("local.fold");
pub fn sum<I:Type+Copy+Drop,F:Field>(rows:scoped domain<I>,term:scoped fn(I)->F !{stop} on(rows))->F !{stop}{return fold(rows,0,fn(state, item)=>state+term(item));}
)";
const std::string prelude = "module m;" + definitions + R"(
domain Fr=field("koala-bear");
domain Ext=field("koala-bear.ext8-binomial3");
math fn square<F:Field>(x:F)->F{return x*x;}
math fn difference<F:Field>(a:F,b:F)->F{return a-b;}
fn custom<I:Type+Copy+Drop,F:Field>(rows:scoped domain<I>,term:scoped fn(I)->F !{stop} on(rows))->F !{stop}{return sum(rows,term)+1;}
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
const std::string program = R"(
pub reduction ∑=sum;
pub fn f<F:Field>(xs:Vector<F>,ys:Vector<F>,a:F,b:F)->F{
  let first=sum(zip(xs,ys),fn((x,_))=>b*x+a);
  return first+(∑ (x,y) in zip(xs,ys), {
    operator *=difference;
    let z=x*y;
    square(z)+a
  });
}
protocol Demo roles(P)(xs:Vector<Fr>@P,ys:Vector<Fr>@P,a:Fr@P,b:Fr@P)->(r:Fr@P){
  return (r=f(xs,ys,a,b));
}
run Run=Demo;
)";
} // namespace
int main() {
  Cases cases;
  cases.run("named and symbolic reductions retain ordinary scoped computations",
            [] {
              auto project = take(check(program));
              success(checkScopedElaboration(project));
              auto closed = take(closeEntry(project, "m::Run"));
              success(checkScopedSpecialization(closed));
              const auto &function = declaration(project, "m::f");
              require(function.body->scopedBindings.size() == 2,
                      "expected one callback per authored body");
              auto report = take(inspectNotations(project, {true, false}));
              require(take(json::parse(report)).getAsObject() &&
                          report.find("reduction") != std::string::npos,
                      "notation inspection lost reduction descriptors");
              require(report.find("fn((x, y)) =>") != std::string::npos,
                      "binder rendering lost the unary tuple pattern");
              require(take(inspectDeclarations(project)).find("reduction<") ==
                          std::string::npos,
                      "obsolete synthetic declaration leaked");
            });
  for (const auto &body :
       {"sum(xs,fn(x)=>x*x)", "custom(xs,fn(x)=>x)", "sum(xs,fn(_)=>1)",
        "sum(zip(xs,xs),fn((x,_))=>x)", "sum(xs,fn(a)=>{let t=a;t+a})",
        "sum(xs,fn(x)=>({let x=a;x})+x)",
        "sum(xs,fn(x)=>if x==a {x} else {a})"})
    cases.run(body, [&] {
      take(check("fn f(xs:Vector<Fr>,a:Fr)->Fr{return " + std::string(body) +
                 ";}"));
    });
  cases.run("local binding selects an ordinary custom finite consumer", [] {
    auto project =
        take(check("reduction ∑=sum;fn f(xs:Vector<Fr>)->Fr{reduction "
                   "∑=custom;return ∑ x in xs,x;}"));
    const auto &op = declaration(project, "m::f").body->operations.back();
    require(op.binding && op.binding->target.declaration.index ==
                              declaration(project, "m::custom").id.index,
            "local reduction binding lost");
  });
  for (unsigned mode = 0; mode != 3; ++mode)
    cases.run("reduction import visibility " + Twine(mode), [&] {
      auto captured = take(capture(
          {{"lib", "module lib;" + definitions + "pub reduction ∑=sum;", {}},
           {"bridge",
            "module bridge;pub use lib::{Vector,sum,reduction ∑};",
            {}},
           {"m",
            std::string("module m;") +
                (mode == 0 ? "use bridge::{Vector,reduction ∑};"
                 : mode == 1
                     ? "use lib as lib;type Vector<F:Field>=lib::Vector<F>;"
                     : "use bridge::{Vector,sum};") +
                "domain Fr=field(\"koala-bear\");fn "
                "f(xs:Vector<Fr>)->Fr{return ∑ x in xs,x;}",
            {}}}));
      auto project = analyze(captured).checkedProject();
      if (mode == 2)
        refuses(std::move(project), "source.notation-visibility");
      else
        take(std::move(project));
    });
  for (const auto &[source, code] :
       std::vector<std::pair<std::string, std::string>>{
           {"reduction ∑=square;", "source.reduction-target"},
           {"fn f(xs:Vector<Fr>)->Fr{return reduce sum[x in xs]{x};}",
            "source.reduction"},
           {"reduction ∑=sum;fn f(xs:Vector<Fr>)->Fr{return ∑ (x,x) in "
            "zip(xs,xs),x;}",
            "source.binding"},
           {"reduction ∑=sum;fn f(xs:Vector<Fr>)->Fr{let r=∑ x in xs,x;return "
            "x;}",
            "source.name"},
           {"reduction ∑=sum;math fn f(xs:Vector<Fr>)->Fr{return ∑ x in xs,x;}",
            "source.mode"},
           {"reduction ∑=sum;fn f(xs:Vector<Fr>,a:Ext)->Fr{return ∑ x in "
            "xs,a;}",
            "source.type"}})
    cases.run(source, [&, source = source, code = code] {
      refuses(check(source), code);
    });
  cases.run("captures follow first use and preserve ignored zip domains", [] {
    auto project = take(check("reduction ∑=sum;fn "
                              "f(xs:Vector<Fr>,ys:Vector<Fr>,a:Fr,b:Fr)->Fr{"
                              "return ∑ (_,x) in zip(xs,ys),(b*x+a+b);}"));
    const auto &body = *declaration(project, "m::f").body;
    const auto &binding = body.scopedBindings.back();
    require(binding.captures.size() == 2, "unexpected capture count");
    const auto &first = body.operations[0], &second = body.operations[1];
    require(std::get<Projection>(first.action).input.index == 3 &&
                std::get<Projection>(second.action).input.index == 2,
            "capture reads lost first-use order");
    const auto &domain = body.domainBindings.back();
    require(domain.children.size() == 2, "ignored row removed from strict zip");
    success(checkScopedElaboration(project));
  });
  cases.run("collections evaluate once in written order before captures", [] {
    auto project = take(check(R"(
reduction ∑=sum;
fn first(xs:Vector<Fr>)->Vector<Fr>{return xs;}
fn second(xs:Vector<Fr>)->Vector<Fr>{return xs;}
fn f(xs:Vector<Fr>,a:Fr)->Fr{return ∑ ((x,y),z) in zip(zip(second(xs),first(xs)),second(xs)),(x*y*z+a);}
)"));
    const auto &body = *declaration(project, "m::f").body;
    for (unsigned i = 0; i != 3; ++i)
      require(body.operations[i].binding &&
                  body.operations[i].binding->target.declaration.index ==
                      declaration(project, i == 1 ? "m::first" : "m::second")
                          .id.index,
              "collection evaluation changed");
    require(std::holds_alternative<Projection>(body.operations[3].action),
            "capture preceded collections");
    success(checkScopedElaboration(project));
  });
  cases.run(
      "local notation in a binder retains its authored lexical scope", [] {
        auto project = take(check(R"(
reduction ∑=sum;operator prefix(75) ⊖=square;
fn f(xs:Vector<Fr>)->Fr{return ∑ x in xs,{
 operator ⊗=difference;operator infixl(70) ⊗=difference;
 operator prefix(75) ⊖=identity; ⊖x ⊗ x
};}
math fn identity(x:Fr)->Fr{return x;}
)"));
        const auto &body = *declaration(project, "m::f")
                                .body->scopedBindings.back()
                                .computation->body;
        auto prefix = llvm::find_if(body.operations, [](const Operation &op) {
          return op.binding && op.binding->symbol == "⊖";
        });
        require(prefix != body.operations.end() &&
                    prefix->binding->target.declaration.index ==
                        declaration(project, "m::identity").id.index,
                "prefix resolved outside its authored scope");
        success(checkScopedElaboration(project));
      });
  cases.run("budgets include ordinary scoped binder work", [] {
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
  cases.run("many binder sites have stable distinct closure identities", [] {
    std::string source = "reduction ∑=sum;fn f(xs:Vector<Fr>)->Fr{";
    for (unsigned i = 0; i != 64; ++i)
      source += "let r" + std::to_string(i) + "=∑ x in xs,(x+1);";
    source += "return r63;}protocol Demo "
              "roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return f(xs);}run Run=Demo;";
    auto first = take(check(source)), second = take(check(source));
    const auto &bindings = declaration(first, "m::f").body->scopedBindings;
    require(bindings.size() == 64, "binder site lost");
    std::set<unsigned> expressions;
    for (const auto &binding : bindings)
      require(expressions.insert(binding.computation->expression).second,
              "binder identity collided");
    auto closed = take(closeEntry(first, "m::Run")),
         other = take(closeEntry(second, "m::Run"));
    require(closed.declarations().size() == other.declarations().size(),
            "unstable specialization count");
    for (unsigned i = 0; i != closed.declarations().size(); ++i)
      require(closed.declarations()[i].symbol == other.declarations()[i].symbol,
              "unstable closed identity");
    auto report = take(inspectNotations(first, {true, false}));
    require(report == take(inspectNotations(first, {true, false})) &&
                report.find("not-emitted") == std::string::npos,
            "inspection lost a scoped occurrence");
  });
  for (const auto &mutation : {"capture", "capture-order", "body-operand",
                               "binding-target", "missing-binding"})
    cases.run(Twine("independent binder witness rejects ") + mutation, [&] {
      auto project = take(check(program));
      auto &body = const_cast<Body &>(*declaration(project, "m::f").body);
      auto &binding = body.scopedBindings.front();
      StringRef change = mutation;
      if (change == "capture")
        binding.captures[0] = binding.captures[1];
      else if (change == "capture-order")
        std::swap(binding.captures[0], binding.captures[1]);
      else if (change == "body-operand") {
        auto &nested = const_cast<Body &>(*binding.computation->body);
        bool changed = false;
        for (auto &op : nested.operations)
          if (auto *call = std::get_if<LocalPrimitive>(&op.action)) {
            if (call->operands.size() == 2) {
              call->operands[0] = call->operands[1];
              changed = true;
              break;
            }
          }
        require(changed, "missing callback operand mutation target");
      } else {
        auto found = llvm::find_if(body.operations, [](const Operation &op) {
          return op.binding && op.binding->scopedSource;
        });
        require(found != body.operations.end(), "missing scoped call");
        if (change == "binding-target")
          found->binding->target.declaration =
              declaration(project, "m::custom").id;
        else
          found->binding.reset();
      }
      auto error = checkScopedElaboration(project);
      require(bool(error), "corrupt binder evidence accepted");
      consumeError(std::move(error));
    });
  return cases.result();
}
