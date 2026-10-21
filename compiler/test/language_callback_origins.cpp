#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
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
domain fn elements<F:Field>(xs:Vector<F>)->domain<F>=domain("elements");
domain fn indices<F:Field>(xs:Vector<F>)->domain<index>=domain("indices");
fn fold<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,
  step:fn(S,item:I)->S effects(stop) where item_from(item,rows)
)->S effects(stop)=finite("local.fold");
math fn total<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,
  step:math fn(S,item:I)->S where item_from(item,rows)
)->S=finite("math.fold");
pub fn first(rows:domain<Fr>,initial:Fr,
  step:fn(item:Fr,Fr)->Fr effects(stop) where item_from(item,rows)
)->Fr effects(stop){return fold(rows,initial,fn(s,x)=>step(x,s));}
pub fn grid(rows:domain<Fr>,columns:domain<Fr>,
  term:fn(row:Fr,column:Fr)->Fr effects(stop)
    where item_from(row,rows),item_from(column,columns)
)->Fr effects(stop){
 return fold(rows,0,fn(s,r)=>s+fold(columns,0,fn(t,c)=>t+term(r,c)));
}
)";
Expected<CheckedProject> check(StringRef source, const Limits &limits = {}) {
  auto captured = capture({{"m", prelude + source.str(), "origins.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
const Declaration &named(const CheckedProject &project, StringRef name) {
  for (const auto &decl : project.declarations())
    if (decl.name == name)
      return decl;
  throw std::runtime_error("missing declaration");
}
void errorIs(Error error, StringRef code) {
  require(bool(error), "mutation accepted");
  auto message = toString(std::move(error));
  require(namesIdentifier(message, code), "unexpected refusal: " + message);
}
} // namespace
int main() {
  Cases cases;
  cases.run("arbitrary slots and independent captured origins close", [] {
    auto project = take(check(R"(
fn permute(rows:domain<Fr>,columns:domain<Fr>,
 body:fn(c:Fr,Fr,r:Fr)->Fr effects(stop) where item_from(r,rows),item_from(c,columns)
)->Fr effects(stop){return grid(rows,columns,fn(r,c)=>body(c,0,r));}
protocol Demo roles(P)(xs:Vector<Fr>@P,ys:Vector<Fr>@P)->(r:Fr@P){
 return permute(elements(xs),elements(ys),fn(a,unused,b)=>a+b+unused);
}run Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
)"));
    auto closed = take(zkc::test::closeProtocolDeployment(project, "m::Run"));
    if (auto error = checkScopedSpecialization(closed))
      throw std::runtime_error(toString(std::move(error)));
    require(named(project, "permute").scopedInputs[0].itemOrigins ==
                std::map<unsigned, unsigned>{{0, 1}, {2, 0}},
            "requirements are not normalized by explicit position");
  });
  cases.run(
      "generic independent item types survive closure and immutable aliases",
      [] {
        auto project = take(check(R"(
fn generic_grid<A:Type+Copy+Drop,B:Type+Copy+Drop>(rows:domain<A>,columns:domain<B>,
 term:fn(a:A,b:B)->Fr effects(stop) where item_from(a,rows),item_from(b,columns))->Fr effects(stop){
 return fold(rows,0,fn(s,r)=>{let alias=r;s+fold(columns,0,fn(t,c)=>t+term(alias,c))});
}
protocol Demo roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){
 return generic_grid(elements(xs),indices(xs),fn(value,i)=>value);
}run Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
)"));
        take(zkc::test::closeProtocolDeployment(project, "m::Run"));
      });
  cases.run("equal-typed state is not an item in the first slot", [] {
    refuses(check(R"(
fn bad(rows:domain<Fr>,step:fn(item:Fr,state:Fr)->Fr effects(stop)
 where item_from(item,rows))->Fr effects(stop){
 return fold(rows,0,fn(state,item)=>step(state,item));
}
)"),
            "source.scoped-domain");
  });
  cases.run("unrestricted callback flows to multiple restricted inputs", [] {
    take(check(R"(
fn free(rows:domain<Fr>,columns:domain<Fr>,term:fn(Fr,Fr)->Fr effects(stop))->Fr effects(stop){
 return grid(rows,columns,term);
}
)"));
  });
  cases.run("partial restriction flows to stronger consumer guarantee", [] {
    take(check(R"(
fn partial(rows:domain<Fr>,columns:domain<Fr>,term:fn(row:Fr,Fr)->Fr effects(stop)
 where item_from(row,rows))->Fr effects(stop){return grid(rows,columns,term);}
)"));
  });
  for (const auto &invocation :
       {"term(r,0)", "term(c,r)", "term(r,r)", "term(r,c+0)"})
    cases.run("independent origin required: " + std::string(invocation), [&] {
      refuses(check(std::string(R"(
fn bad(rows:domain<Fr>,columns:domain<Fr>,term:fn(row:Fr,column:Fr)->Fr effects(stop)
 where item_from(row,rows),item_from(column,columns))->Fr effects(stop){
 return grid(rows,columns,fn(r,c)=>)") +
                    invocation + ");}"),
              "source.scoped-domain");
    });
  cases.run("partially guaranteed forwarding refuses", [] {
    refuses(check(R"(
fn consumer(rows:domain<Fr>,term:fn(row:Fr,Fr)->Fr effects(stop)
 where item_from(row,rows))->Fr effects(stop){return fold(rows,0,fn(s,r)=>term(r,s));}
fn bad(rows:domain<Fr>,columns:domain<Fr>,term:fn(row:Fr,column:Fr)->Fr effects(stop)
 where item_from(row,rows),item_from(column,columns))->Fr effects(stop){return consumer(rows,term);}
)"),
            "source.scoped-domain");
  });
  cases.run("actual domains substitute before subset comparison", [] {
    take(check(R"(
fn forward(columns:domain<Fr>,rows:domain<Fr>,term:fn(a:Fr,b:Fr)->Fr effects(stop)
 where item_from(a,rows),item_from(b,columns))->Fr effects(stop){return grid(rows,columns,term);}
)"));
    refuses(check(R"(
fn bad(columns:domain<Fr>,rows:domain<Fr>,term:fn(a:Fr,b:Fr)->Fr effects(stop)
 where item_from(a,rows),item_from(b,columns))->Fr effects(stop){return grid(columns,rows,term);}
)"),
            "source.scoped-domain");
  });
  cases.run("input labels and clause order are alpha invariant", [] {
    auto project = take(check(R"(
fn renamed(a:domain<Fr>,b:domain<Fr>,body:fn(x:Fr,y:Fr)->Fr effects(stop)
 where item_from(y,b),item_from(x,a))->Fr effects(stop){return grid(a,b,body);}
)"));
    require(named(project, "renamed").scopedInputs[0].signature ==
                named(project, "grid").scopedInputs[0].signature,
            "labels participate in semantic identity");
  });
  cases.run("local conditions end before any following port category", [] {
    take(check(R"(
fn parse(body:fn(x:Fr)->Fr effects() where item_from(x,rows),item_from:Fr,
 rows:domain<Fr>,other:math fn(y:Fr)->Fr where item_from(y,rows),last:bool)->Fr effects(){
 return item_from;
}
fn empty(body:fn(Fr)->Fr effects() where (),x:Fr)->Fr effects(){return body(x);}
)"));
  });
  for (StringRef expression : {"if go {fold(rows,0,step)} else {0}",
                               "invoke(0,fn(_)=>fold(rows,0,step))"})
    cases.run("restricted callback forwarding inside a region: " + expression,
              [&] {
                auto source = R"(
fn invoke(x:Fr,body:fn(Fr)->Fr effects(stop))->Fr effects(stop){return body(x);}
fn forward(go:bool,rows:domain<Fr>,columns:domain<Fr>,
 step:fn(Fr,item:Fr)->Fr effects(stop) where item_from(item,rows)
)->Fr effects(stop){return )" +
                              expression.str() + R"(;}
protocol Demo roles(P)(go:bool@P,xs:Vector<Fr>@P)->(r:Fr@P){
 return forward(go,elements(xs),elements(xs),fn(state,item)=>state+item);
}run Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
)";
                auto project = take(check(source));
                if (auto error = checkScopedElaboration(project))
                  throw std::runtime_error(toString(std::move(error)));
                auto closed =
                    take(zkc::test::closeProtocolDeployment(project, "m::Run"));
                if (auto error = checkScopedSpecialization(closed))
                  throw std::runtime_error(toString(std::move(error)));
                source.replace(source.find("fold(rows,0,step)"),
                               StringRef("fold(rows,0,step)").size(),
                               "fold(columns,0,step)");
                refuses(check(source), "source.scoped-domain");
              });
  cases.run("origin clause heads remain ordinary declaration names", [] {
    take(check(
        "fn on(x:Fr)->Fr{return x;} fn item_from(x:Fr)->Fr{return on(x);}"));
  });
  cases.run("outer origin clause is diagnosed at its owning boundary", [] {
    refuses(
        check("fn bad(rows:domain<Fr>)->Fr where item_from(x,rows){return 0;}"),
        "source.finite-domain");
  });
  const std::vector<std::pair<std::string, std::string>> invalid = {
      {"fn(x:Fr,x:Fr)->Fr effects()", "source.duplicate"},
      {"fn(Fr)->Fr effects() where item_from(x,rows)", "source.finite-domain"},
      {"fn(x:Fr)->Fr effects() where item_from(result,rows)",
       "source.finite-domain"},
      {"fn(x:Fr)->Fr effects() where item_from(x,missing)",
       "source.finite-domain"},
      {"fn(x:Fr)->Fr effects() where item_from(x,body)",
       "source.finite-domain"},
      {"fn(x:bool)->Fr effects() where item_from(x,rows)",
       "source.finite-domain"},
      {"fn(x:Fr)->Fr effects() where item_from(x,rows),item_from(x,rows)",
       "source.finite-domain"},
      {"fn(x:Fr)->Fr effects() where item_from(x,rows),item_from(x,other)",
       "source.finite-domain"},
      {"fn(x:Fr)->Fr effects() where unknown(x,rows)", "source.finite-domain"},
      {"fn(x:Fr)->Fr effects() where item_from(x,rows),unknown(x,rows)",
       "source.finite-domain"},
      {"fn(x:Fr)->Fr effects() where (item_from(x,rows))", "source.syntax"},
      {"fn(x:Fr)->Fr effects() where item_from(0,rows)", "source.name"},
      {"fn(x:Fr)->Fr effects() where item_from(x.0,rows)", "source.syntax"},
      {"fn(x:Fr)->Fr effects() on(rows)", "source.syntax"},
      {"fn(x:Fr)->Fr where item_from(x,rows) effects()", "source.effect"},
  };
  for (const auto &test : invalid)
    cases.run("reject callback contract: " + test.first, [&] {
      refuses(check("interface Invalid{fn "
                    "member(rows:domain<Fr>,other:domain<Fr>,body:" +
                    test.first + ")->Fr;}"),
              test.second);
    });
  cases.run("callback labels obey static parameter shadowing", [] {
    refuses(check(R"(
interface Invalid<T:Type>{fn member(body:fn(T:Fr)->Fr effects())->Fr;}
)"),
            "source.shadow");
  });
  cases.run("registered ABI requires last fold slot even for equal types", [] {
    refuses(check(R"(
fn bad(rows:domain<Fr>,initial:Fr,step:fn(item:Fr,Fr)->Fr effects(stop)
 where item_from(item,rows))->Fr effects(stop)=finite("local.fold");
)"),
            "source.finite");
  });
  cases.run("interface contracts compare normalized slots", [] {
    take(check(R"(
interface Grid{
 fn run(rows:domain<Fr>,columns:domain<Fr>,term:fn(r:Fr,c:Fr)->Fr effects(stop)
 where item_from(r,rows),item_from(c,columns))->Fr effects(stop);
}
module Impl:Grid{
 fn run(a:domain<Fr>,b:domain<Fr>,body:fn(x:Fr,y:Fr)->Fr effects(stop)
 where item_from(y,b),item_from(x,a))->Fr effects(stop){return grid(a,b,body);}
}
protocol Demo roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){
 return Impl::run(elements(xs),elements(xs),fn(a,b)=>a+b);
}run Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
)"));
  });
  for (const auto &clause :
       {"", " where item_from(c,rows)", " where item_from(r,columns)"})
    cases.run("module rejects changed callback promise" + std::string(clause),
              [&] {
                refuses(check(std::string(R"(
interface Contract{fn run(rows:domain<Fr>,columns:domain<Fr>,body:fn(r:Fr,c:Fr)->Fr effects(stop)
 where item_from(r,rows))->Fr effects(stop);}
module Impl:Contract{fn run(rows:domain<Fr>,columns:domain<Fr>,body:fn(r:Fr,c:Fr)->Fr effects(stop))") +
                              clause + ")->Fr effects(stop){return 0;}}"),
                        "source.conformance");
              });
  cases.run("associated callback contracts survive generic substitution", [] {
    auto project = take(check(R"(
interface Contract<T:Type+Copy+Drop>{
 type Item:Copy+Drop;
 fn run(rows:domain<Item>,body:fn(item:Item)->T effects(stop)
   where item_from(item,rows))->T effects(stop);
}
module Impl<F:Field>:Contract<F>{
 type Item:Copy+Drop=F;
 fn run(rows:domain<Item>,body:fn(item:Item)->F effects(stop)
   where item_from(item,rows))->F effects(stop){
   return fold(rows,0,fn(state,item)=>state+body(item));
 }
}
)"));
    if (auto error = checkScopedElaboration(project))
      throw std::runtime_error(toString(std::move(error)));
    auto &implementation = const_cast<Declaration &>(named(project, "Impl"));
    implementation.implementation->arguments.front() = Type{};
    errorIs(checkScopedElaboration(project), "source.scoped-witness");
  });
  for (const auto &contract :
       {std::pair{"origins", "rows:domain<Fr>,body:fn(item:Fr)->Fr "
                             "effects(stop) where item_from(item,rows)"},
        std::pair{"ceiling", "rows:domain<Fr>,body:fn(Fr)->Fr effects()"},
        std::pair{"mode", "rows:domain<Fr>,body:math fn(Fr)->Fr"},
        std::pair{"input type",
                  "rows:domain<Fr>,body:fn(index)->Fr effects(stop)"},
        std::pair{"result type",
                  "rows:domain<Fr>,body:fn(Fr)->index effects(stop)"},
        std::pair{"argument order",
                  "body:fn(Fr)->Fr effects(stop),rows:domain<Fr>"}})
    cases.run(
        "independent module callback contract: " + std::string(contract.first),
        [&] {
          const std::string offered =
              "rows:domain<Fr>,body:fn(Fr)->Fr effects(stop)";
          const std::string required = contract.second;
          auto project = take(check("interface Required{fn run(" + required +
                                    ")->Fr effects();}"
                                    "interface Offered{fn run(" +
                                    offered +
                                    ")->Fr effects();}"
                                    "module Impl:Offered{fn run(" +
                                    offered +
                                    ")->Fr effects(){return 0;}}"
                                    "module Anchor:Required{fn run(" +
                                    required + ")->Fr effects(){return 0;}}"));
          // Every declaration still agrees with its own retained source. Only
          // the relation between the module and its selected interface is
          // changed.
          auto &implementation =
              const_cast<Declaration &>(named(project, "Impl"));
          implementation.implementation =
              named(project, "Anchor").implementation;
          errorIs(checkScopedElaboration(project), "source.scoped-witness");
        });
  for (const auto &outer : {"", " where ()", " where 1<=N"})
    cases.run("callback where preserves natural inference" + std::string(outer),
              [&] {
                auto source = std::string(R"(
fn natural<N:nat>(rows:domain<Fr>,body:fn(x:Fr)->Fr effects() where item_from(x,rows),
 xs:[bool;N])->bool)") + outer +
                              "{return xs[0];}";
                if (StringRef(outer) == " where ()")
                  refuses(check(source), "source.bound");
                else {
                  auto project = take(check(source));
                  require(named(project, "natural").bounds.size() == 1,
                          "inner where changed inferred natural requirements");
                }
              });
  for (const auto &outer :
       {"", " where ()", " where zkc::algebra::TwoAdicField(F)"})
    cases.run(
        "callback where preserves catalog inference" + std::string(outer), [&] {
          auto source = std::string(R"(
fn catalog<F:Field>(rows:domain<F>,body:fn(x:F)->F effects() where item_from(x,rows),n:index)->F)") +
                        outer + "{return kernel<F>(\"poly.domain_root\",n);}";
          if (StringRef(outer) == " where ()")
            refuses(check(source), "source.kernel");
          else {
            auto project = take(check(source));
            require(named(project, "catalog").capabilityBounds.size() == 1,
                    "inner where changed inferred catalog requirements");
          }
        });
  for (unsigned size : {0u, 1u})
    cases.run("concrete callers discharge outer natural conditions " +
                  Twine(size),
              [&] {
                auto source = std::string(R"(
fn natural<N:nat>(rows:domain<Fr>,body:fn(x:Fr)->Fr effects() where item_from(x,rows),
 xs:[bool;N])->bool where 1<=N {return xs[0];}
fn caller(rows:domain<Fr>,xs:[bool;)") +
                              std::to_string(size) +
                              "])->bool{return natural(rows,fn(x)=>x,xs);}";
                if (size)
                  take(check(source));
                else
                  refuses(check(source), "source.bound");
              });
  cases.run("multiple total index bounds survive captures and closure", [] {
    auto project = take(check(R"(
math fn at(xs:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){return intrinsic<Vector<Fr>>("container.at",xs,i);}
math fn indexed(rows:domain<index>,columns:domain<index>,
 body:math fn(r:index,c:index)->Fr where item_from(r,rows),item_from(c,columns))->Fr{
 return total(rows,0,fn(s,r)=>s+total(columns,0,fn(t,c)=>t+body(r,c)));
}
math fn work(xs:Vector<Fr>,ys:Vector<Fr>)->Fr{
 return indexed(indices(xs),indices(ys),fn(r,c)=>at(xs,r)+at(ys,c));
}
protocol Demo roles(P)(xs:Vector<Fr>@P,ys:Vector<Fr>@P)->(r:Fr@P){return work(xs,ys);}run Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
)"));
    take(zkc::test::closeProtocolDeployment(project, "m::Run"));
  });
  for (unsigned mutation = 0; mutation < 3; ++mutation)
    cases.run("independent formal contract mutation " + Twine(mutation), [&] {
      auto project = take(check(""));
      auto &decl = const_cast<Declaration &>(named(project, "grid"));
      auto &origins = decl.scopedInputs[0].itemOrigins;
      if (mutation == 0)
        origins = {{1, 0}, {0, 1}};
      else if (mutation == 1)
        origins[0] = 1;
      else
        origins.erase(1);
      errorIs(checkScopedElaboration(project), "source.scoped-witness");
    });
  cases.run(
      "inspection separates labels and canonical origin requirements", [] {
        auto project = take(check(""));
        auto report = take(inspectDeclarations(project));
        auto json = take(json::parse(report));
        // Inspect the serialized contract, including absence of the old schema.
        require(report.find("\"on\"") == std::string::npos &&
                    report.find("\"item_origins\"") != std::string::npos &&
                    report.find("\"input_labels\"") != std::string::npos,
                "inspection schema did not migrate");
        auto *declarations = json.getAsArray();
        require(declarations && declarations->size() == 3,
                "public inventory differs");
        const auto *first = (*declarations)[1].getAsObject();
        const auto *firstCallback =
            (*first->getArray("scoped_inputs"))[0].getAsObject();
        const auto *firstLabels = firstCallback->getArray("input_labels");
        require(firstLabels && firstLabels->size() == 2 &&
                    (*firstLabels)[1].getAsNull(),
                "unnamed callback input is not null");
        const auto *grid = (*declarations)[2].getAsObject();
        require(grid, "missing grid inspection");
        const auto *parameters = grid->getArray("scoped_inputs");
        require(parameters && parameters->size() == 1,
                "callback inventory differs");
        const auto *callback = (*parameters)[0].getAsObject();
        const auto *labels = callback->getArray("input_labels");
        const auto *origins = callback->getArray("item_origins");
        require(labels && labels->size() == 2 &&
                    (*labels)[0].getAsString() == "row" &&
                    (*labels)[1].getAsString() == "column",
                "source labels differ");
        require(origins && origins->size() == 2, "origin map coverage differs");
        for (unsigned i = 0; i < 2; ++i) {
          const auto *origin = (*origins)[i].getAsObject();
          require(origin && origin->size() == 2 &&
                      origin->getInteger("input") == i &&
                      origin->getInteger("domain") == i,
                  "canonical origin schema differs");
        }
      });
  cases.run("abstract item origins remain anchored to authored selectors", [] {
    auto project = take(check(R"(
interface Grid {
 fn run(rows:domain<Fr>,columns:domain<Fr>,
   term:fn(row:Fr,column:Fr)->Fr effects(stop)
     where item_from(row,rows),item_from(column,columns)
 )->Fr effects(stop);
}
)"));
    bool mutated = false;
    for (const auto &decl : project.declarations())
      if (decl.abstract && decl.name == "run") {
        auto &changed = const_cast<Declaration &>(decl);
        changed.scopedInputs.front().itemOrigins = {{0, 1}, {1, 0}};
        mutated = true;
      }
    require(mutated, "missing abstract contract fixture");
    errorIs(checkScopedElaboration(project), "source.scoped-witness");
  });
  cases.run("witness rechecking respects work limits", [] {
    auto project = take(check(""));
    Limits limits;
    limits.work = 1;
    errorIs(checkScopedElaboration(project, limits), "source.limit");
  });
  cases.run("parsing and checking respect lowered limits", [] {
    Limits limits;
    limits.tokens = 50;
    refuses(check("", limits), "source.limit");
    limits = {};
    limits.work = 200;
    refuses(check("", limits), "source.limit");
  });
  return cases.result();
}
