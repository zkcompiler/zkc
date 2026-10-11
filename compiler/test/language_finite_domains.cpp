#include "../lib/Language/BodyMapping.h"
#include "../lib/Language/BodySummary.h"
#include "../lib/Language/ClosureInputs.h"
#include "../lib/Language/DomainClosure.h"
#include "../lib/Language/DomainWitness.h"
#include "support/NativeCases.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/Project.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
const std::string prelude = R"(module m;
type Vector<F:Field>=builtin("vector",F);
type Groups<G:Group>=builtin("groups",G);
type Matrix<F:Field>=builtin("matrix",F);
type Sequence<T:Type+Copy+Drop>=builtin("sequence",T);
pub domain fn elements<F:Field>(xs:Vector<F>)->domain<F>=domain("elements");
pub domain fn groups<G:Group>(xs:Groups<G>)->domain<G>=domain("elements");
pub domain fn indices<F:Field>(xs:Vector<F>)->domain<index>=domain("indices");
pub domain fn range(lo:index,hi:index)->domain<index>=domain("range");
pub domain fn zip<A:Type+Copy+Drop,B:Type+Copy+Drop>(a:domain<A>,b:domain<B>)->domain<(A,B)>=domain("zip");
)";
Expected<CheckedProject> check(StringRef source) {
  auto captured = capture({{"m", prelude + source.str(), "domains.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
const Declaration &declarationNamed(const CheckedProject &project,
                                    StringRef name) {
  for (const auto &decl : project.declarations())
    if (decl.qualifiedName == name)
      return decl;
  throw std::runtime_error("missing declaration");
}
} // namespace
int main() {
  Cases cases;

  const std::string finitePrelude = R"(
domain Fr=field("koala-bear");
fn fold<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,step:fn(S,item:I)->S effects(stop) where item_from(item, rows))->S effects(stop)=finite("local.fold");
fn apply<A:Type,B:Type>(x:A,body:fn(A)->B effects(stop))->B effects(stop){return body(x);}
)";
  const std::string notationPrelude = finitePrelude + R"(
fn sum<I:Type+Copy+Drop>(rows:domain<I>,term:fn(item:I)->Fr effects(stop) where item_from(item, rows))->Fr effects(stop){return fold(rows,0,fn(state, item)=>state+term(item));}
fn fold_where<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,keep:fn(item:I)->bool effects(stop) where item_from(item, rows),step:fn(S,item:I)->S effects(stop) where item_from(item, rows))->S effects(stop)=finite("local.fold_where");
fn sum_where<I:Type+Copy+Drop>(rows:domain<I>,keep:fn(item:I)->bool effects(stop) where item_from(item, rows),term:fn(item:I)->Fr effects(stop) where item_from(item, rows))->Fr effects(stop){return fold_where(rows,0,keep,fn(state, item)=>state+term(item));}
)";
  cases.run(
      "indexed callbacks capture static elements and dynamic containers", [&] {
        auto project = take(check(notationPrelude + R"(
fn at<F:Field>(xs:Vector<F>,i:index)->F=primitive("vector.get");
indexing xs[i]=at(xs,i);
struct State{pub xs:Vector<Fr>,pub fixed:[Fr;2]}
fn work(state:State)->Fr{return sum(indices(state.xs),fn(i)=>state.xs[i]+state.fixed[0]);}
protocol Demo roles(P)(state:State@P)->(r:Fr@P){return work(state);}run Run=Demo;
)"));
        take(closeEntry(project, "m::Run"));
        const auto &work = declarationNamed(project, "m::work");
        bool fixed = false, container = false;
        for (const auto &binding : work.body->scopedBindings)
          for (auto capture : binding.captures)
            for (const auto &operation : work.body->operations)
              if (operation.results.size() == 1 &&
                  operation.results[0].index == capture.index)
                if (const auto *projection =
                        std::get_if<Projection>(&operation.action)) {
                  fixed |= projection->path == std::vector<unsigned>{1, 0};
                  container |= projection->path == std::vector<unsigned>{0};
                }
        require(fixed && container, "indexed capture paths changed");
      });
  cases.run("scoped call statements retain their authored occurrence", [&] {
    take(check(notationPrelude + R"(
fn note(value:Fr)->(){return ();}
fn at<F:Field>(xs:Vector<F>,i:index)->F=primitive("vector.get");
indexing xs[i]=at(xs,i);
fn work(xs:Vector<Fr>)->Fr{return sum(indices(xs),fn(i)=>{note(0);let ignored=xs[i];0});}
)"));
  });
  for (unsigned mutation = 0; mutation < 11; ++mutation)
    cases.run(
        "indexed scoped source mutation " + std::to_string(mutation), [&] {
          auto source = notationPrelude + R"(
fn at<F:Field>(xs:Vector<F>,i:index)->F=primitive("vector.get");
indexing xs[i]=at(xs,i);
)" +
                        std::string(mutation == 8 ? R"(
fn work(xs:Vector<Fr>)->Fr{return sum(indices(xs),fn(i)=>{let value=xs[i];value});}
)"
                                                  : R"(
fn work(xs:Vector<Fr>)->Fr{return sum(indices(xs),fn(i)=>xs[i]);}
)");
          auto project = take(check(source));
          auto &outer =
              const_cast<Body &>(*declarationNamed(project, "m::work").body);
          bool changed = false;
          for (auto &scoped : outer.scopedBindings)
            if (scoped.computation) {
              auto &body = const_cast<Body &>(*scoped.computation->body);
              std::optional<Operation> extra;
              for (auto &operation : body.operations)
                if (operation.binding && operation.binding->notation) {
                  if (mutation == 0)
                    operation.binding->notation->arity = 3;
                  else if (mutation == 1)
                    operation.binding->family[0] = "forged";
                  else if (mutation == 2)
                    operation.binding.reset();
                  else if (mutation == 3) {
                    operation.binding->family[0] = "forged";
                    ++operation.span.begin;
                  } else if (mutation == 4)
                    ++operation.span.source.index;
                  else if (mutation == 5 || mutation == 8) {
                    auto result = operation.results.front();
                    for (auto it = body.expressionValues.begin();
                         it != body.expressionValues.end();)
                      if (it->second.index == result.index)
                        it = body.expressionValues.erase(it);
                      else
                        ++it;
                  } else if (mutation == 6)
                    body.results.front() = ValueId{0};
                  else if (mutation == 7)
                    operation.binding->notation.reset();
                  else {
                    extra = operation;
                    if (mutation == 9)
                      extra->binding->family[0] = "forged";
                  }
                  changed = true;
                }
              if (extra) {
                auto result = body.values[extra->results.front().index];
                extra->results.front() = ValueId{unsigned(body.values.size())};
                body.values.push_back(std::move(result));
                body.operations.push_back(std::move(*extra));
              }
            }
          require(changed, "missing indexed callback");
          auto error = checkScopedElaboration(project);
          require(bool(error), "forged indexed binding accepted");
          consumeError(std::move(error));
        });
  cases.run("finite notation uses ordinary scoped calls", [&] {
    auto project = take(check(notationPrelude + R"(
reduction ∑=sum,sum_where;
protocol Demo roles(P)(xs:Vector<Fr>@P,ys:Vector<Fr>@P,enabled:bool@P)->(r:Fr@P){
 let one@P=∑ x ∈ xs, x*x;
 let two@P=∑ (x ∈ xs) (y ∈ ys) with enabled, x*y;
 let three@P=∑ x in xs, (∑ y in ys, x*y);
 return one+two+three;
}run Run=Demo;
)"));
    take(closeEntry(project, "m::Run"));
    auto report = take(inspectNotations(project, {true, false}));
    require(report.find("m::sum_where") != std::string::npos,
            "filtered target lost from inspection");
  });
  for (const auto &source :
       {std::string("reduction ⨁=sum,sum_where;fn "
                    "work(xs:Vector<Fr>)->Fr{return ⨁ x ∈ xs with true,x*x;}"),
        std::string("reduction ∑=sum;fn work(xs:Vector<Fr>)->Fr{return ∑ (x in "
                    "xs) (y in xs) (z in xs),x*y*z;}"),
        std::string("reduction ∑=sum;fn work(xs:Vector<Fr>)->Fr{return ∑ "
                    "((x,y) in zip(xs,xs)) (z in xs),x*y*z;}"),
        std::string(
            "interface Scale{math fn apply(x:Fr)->Fr;}fn "
            "custom<C:Scale>(rows:domain<Fr>,term:"
            "fn(item:Fr)->Fr effects(stop) where item_from(item, rows))->Fr "
            "effects(stop){return "
            "sum(rows,fn(x)=>C::apply(term(x)));}fn "
            "work<C:Scale>(xs:Vector<Fr>)->Fr{reduction "
            "∑=custom<C>;return ∑ x∈xs,x;}"),
        std::string(
            "math fn math_fold<I:Type+Copy+Drop>(rows:"
            "domain<I>,initial:Fr,step:math fn(Fr,item:I)->Fr "
            "where item_from(item, rows))->Fr=finite(\"math.fold\");math fn "
            "total<I:Type+Copy+Drop>(rows:domain<I>,term:math "
            "fn(item:I)->Fr where item_from(item, rows))->Fr{return "
            "math_fold(rows,0,fn(state, "
            "x)=>state+term(x));}math fn work(xs:Vector<Fr>)->Fr{reduction "
            "∑=total;return ∑ x∈xs,x*x;}")})
    cases.run("general finite notation " + source,
              [&] { take(check(notationPrelude + source)); });
  for (const auto &[source, code] :
       std::vector<std::pair<std::string, std::string>>{
           {"reduction ∑=sum;fn work(xs:Vector<Fr>)->Fr{return ∑ x in xs with "
            "true,x;}",
            "source.reduction-target"},
           {"reduction ∑=sum,sum_where;fn work(xs:Vector<Fr>)->Fr{reduction "
            "∑=sum;return ∑ x in xs with true,x;}",
            "source.reduction-target"},
           {"reduction ∑=sum;reduction ∑=sum_where;",
            "source.reduction-target"},
           {"fn other<I:Type+Copy+Drop>(rows:domain<I>,term:"
            "fn(item:I)->Fr effects(stop) where item_from(item, rows))->Fr "
            "effects(stop){return "
            "sum(rows,term);}reduction ∑=sum;reduction ∑=other;fn "
            "work(xs:Vector<Fr>)->Fr{return ∑ x in xs,x;}",
            "source.notation-ambiguous"},
           {"reduction ∑=sum,sum;", "source.reduction-target"},
           {"reduction ∑=sum<Fr>,sum_where<index>;", "source.reduction-target"},
           {"reduction ∑=sum;fn work(xs:Vector<Fr>)->Fr{return ∑ (x in xs) (y "
            "in [x]),x*y;}",
            "source.name"}})
    cases.run("finite notation refusal " + source,
              [&, source = source, code = code] {
                refuses(check(notationPrelude + source), code);
              });
  for (const auto &source :
       {"reduction *=sum;", "operator prefix(75) ∈=sum;",
        "reduction ∑=sum;fn work(xs:Vector<Fr>,x:Fr)->Fr{return ∑ (x in xs) (y "
        "in [x]),x*y;}"})
    cases.run(std::string("reserved or ambiguous binder ") + source, [&] {
      auto result = check(notationPrelude + source);
      require(!result, "ambiguous or reserved syntax accepted");
      consumeError(result.takeError());
    });
  cases.run("independent domains permit their own lexical shadowing", [&] {
    take(check(notationPrelude + R"(
reduction ∑=sum;
fn work(xs:Vector<Fr>,x:Fr)->Fr{return ∑ (x in xs) (y in {let x:Fr=1;[x]}),x*y;}
)"));
  });
  for (unsigned mutation = 0; mutation != 4; ++mutation)
    cases.run("finite binding source witness " + std::to_string(mutation), [&] {
      auto project = take(check(notationPrelude + R"(
reduction ∑=sum,sum_where;
fn work(xs:Vector<Fr>)->Fr{return ∑ x in xs with true,x;}
)"));
      auto &body =
          const_cast<Body &>(*declarationNamed(project, "m::work").body);
      auto found = llvm::find_if(body.operations, [](const Operation &op) {
        return op.binding && op.binding->notation.has_value();
      });
      require(found != body.operations.end(), "missing reduction call");
      if (mutation == 0)
        found->binding->filteredReduction = false;
      if (mutation == 1)
        found->binding->family[0] = "fabricated";
      if (mutation == 2)
        found->binding->notation->arity = 1;
      if (mutation == 3)
        std::swap(found->binding->scopedArguments[0],
                  found->binding->scopedArguments[1]);
      auto error = checkScopedElaboration(project);
      require(bool(error), "corrupt finite binding accepted");
      consumeError(std::move(error));
    });
  for (const auto &input : {std::string("xs"), std::string("keep(xs)"),
                            std::string("{xs}"), std::string("record.values"),
                            std::string("array"), std::string("[1,2]")})
    cases.run("collection conversion " + input, [&] {
      auto project = take(check(finitePrelude + R"(
struct Record {pub values:Vector<Fr>}
fn keep(xs:Vector<Fr>)->Vector<Fr>{return xs;}
fn work(xs:Vector<Fr>,record:Record,array:[Fr;2])->Fr{
 return fold()" + input + R"(,0,fn(state, item)=>state+item);
}
protocol Demo roles(P)(xs:Vector<Fr>@P,record:Record@P,array:[Fr;2]@P)->(r:Fr@P){return work(xs,record,array);}run Run=Demo;
)"));
      take(closeEntry(project, "m::Run"));
    });
  cases.run("domain factories use the same collection conversion", [&] {
    auto project = take(check(finitePrelude + R"(
domain fn paired(xs:Vector<Fr>,ys:[Fr;2])->domain<(Fr,Fr)>{return zip(xs,ys);}
protocol Demo roles(P)(xs:Vector<Fr>@P,ys:[Fr;2]@P)->(r:Fr@P){return fold(paired(xs,ys),0,fn(state, (a,b))=>state+a*b);}run Run=Demo;
)"));
    take(closeEntry(project, "m::Run"));
  });
  for (unsigned mutation = 0; mutation != 5; ++mutation)
    cases.run(
        "collection conversion source witness " + std::to_string(mutation),
        [&] {
          auto project = take(check(finitePrelude + R"(
fn work(xs:Vector<Fr>,ys:Vector<Fr>)->Fr{return fold(xs,0,fn(state, item)=>state+item);}
)"));
          auto &body =
              const_cast<Body &>(*declarationNamed(project, "m::work").body);
          auto &domain = body.domainBindings.front();
          if (mutation == 0)
            domain.expression = 999;
          if (mutation == 1)
            domain.axis = 1;
          if (mutation == 2)
            domain.operands.front() = ValueId{1};
          if (mutation == 3)
            domain.kind = DomainBinding::Kind::SourceArray;
          if (mutation == 4)
            domain.item = Type{};
          auto error = checkScopedElaboration(project);
          require(bool(error), "corrupt collection conversion accepted");
          require(toString(std::move(error)).find("source.scoped-witness") !=
                      std::string::npos,
                  "wrong collection conversion refusal");
        });
  for (unsigned mutation = 0; mutation != 10; ++mutation)
    cases.run(
        "nested collection source witness " + std::to_string(mutation), [&] {
          auto project = take(check(finitePrelude + R"(
fn work(xs:Vector<Fr>,ys:Vector<Fr>)->Fr{
 return fold(zip(b=ys,a=xs),0,fn(state, (x,y))=>state+x*y);
}
)"));
          auto &body =
              const_cast<Body &>(*declarationNamed(project, "m::work").body);
          auto &application = body.domainBindings.back();
          auto &child = body.domainBindings[application.children[0]];
          if (mutation == 0)
            child.expression = 999;
          if (mutation == 1)
            child.operands[0] =
                body.domainBindings[application.children[1]].operands[0];
          if (mutation == 2)
            std::swap(application.children[0], application.children[1]);
          if (mutation == 3)
            child.kind = DomainBinding::Kind::SourceArray;
          if (mutation == 4)
            child.item = Type{};
          if (mutation == 5)
            std::swap(application.argumentOrder[0],
                      application.argumentOrder[1]);
          if (mutation == 6)
            application.factory = CallableReference{
                declarationNamed(project, "m::elements").id, {}};
          if (mutation == 7)
            application.arguments[0] = Type{};
          if (mutation == 8)
            application.children[0] = body.domainBindings.size();
          if (mutation == 9)
            application.children[0] = body.domainBindings.size() - 1;
          auto error = checkScopedElaboration(project);
          require(bool(error), "corrupt nested conversion accepted");
          require(toString(std::move(error)).find("source.scoped-witness") !=
                      std::string::npos,
                  "wrong nested conversion refusal");
        });
  cases.run("nested factories retain authored data operands", [&] {
    auto project = take(check(finitePrelude + R"(
fn work(xs:Vector<Fr>,ys:Vector<Fr>)->Fr{
 return fold(zip(elements(xs),elements(ys)),0,fn(state, (x,y))=>state+x*y);
}
)"));
    auto &body = const_cast<Body &>(*declarationNamed(project, "m::work").body);
    auto &application = body.domainBindings.back();
    auto &left = body.domainBindings[application.children[0]];
    left.operands[0] = body.domainBindings[application.children[1]].operands[0];
    auto error = checkScopedElaboration(project);
    require(bool(error), "changed factory data operand accepted");
    consumeError(std::move(error));
  });
  for (const auto &type :
       {std::string("Matrix<Fr>"), std::string("Fr"), std::string("bool")})
    cases.run("no implicit traversal for " + type, [&] {
      refuses(check(finitePrelude + "fn bad(xs:" + type +
                    ")->Fr{return fold(xs,0,fn(state, item)=>state);}"),
              "source.finite-domain");
    });
  for (const auto &body :
       {std::string("return fold(rows,0,fn(s, x)=>s+term(x));"),
        std::string("let alias=rows;return fold(alias,0,fn(s, x)=>s+term(x));"),
        std::string(
            "return fold(step=fn(s, x)=>s+term(x),initial=0,rows=rows);"),
        std::string("return fold(rows,0,fn(s, x)=>apply(s,fn(t)=>t+term(x)));"),
        std::string("return fold(rows,0,fn(s, x)=>{let value=if flag {term(x)} "
                    "else {0};s+value});"),
        std::string(
            "return fold(rows,0,fn(s, x)=>{let mut result:Fr=s;for j in "
            "0..2 {result=result+term(x);}result});")})
    cases.run("restricted item forwarding " + body, [&] {
      auto project = take(check(finitePrelude + R"(
fn sum(rows:domain<Fr>,flag:bool,term:fn(item:Fr)->Fr effects(stop) where item_from(item, rows))->Fr effects(stop){
)" + body + R"(
}
fn reordered(unused:domain<Fr>,rows:domain<Fr>,term:fn(item:Fr)->Fr effects(stop) where item_from(item, rows))->Fr effects(stop){return sum(rows,true,term);}
protocol Demo roles(P)(xs:Vector<Fr>@P,shift:Fr@P)->(r:Fr@P){return reordered(elements(xs),elements(xs),fn(x)=>x+shift);}run Run=Demo;
)"));
      take(closeEntry(project, "m::Run"));
    });
  for (const auto &body :
       {std::string("return term(0);"), std::string("return apply(0,term);"),
        std::string("return fold(b,0,fn(s, x)=>s+term(x));"),
        std::string("return fold(a,0,fn(s, x)=>s+term(x+1));"),
        std::string("return fold(a,0,fn(s, x)=>apply(x,fn(y)=>s+term(y)));"),
        std::string("return fold(a,0,fn(s, x)=>{let mut y=x;for i in 0..2 "
                    "{y=term(y);}s+y});")})
    cases.run("restricted item refusal " + body, [&] {
      refuses(check(finitePrelude + R"(
fn invalid(a:domain<Fr>,b:domain<Fr>,term:fn(item:Fr)->Fr effects(stop) where item_from(item, a))->Fr effects(stop){
)" + body + "}"),
              "source.scoped-domain");
    });
  cases.run("unrestricted callbacks satisfy a restricted consumer", [&] {
    take(check(finitePrelude + R"(
fn wrapper(rows:domain<Fr>,step:fn(Fr,Fr)->Fr effects(stop))->Fr effects(stop){return fold(rows,0,step);}
)"));
  });
  cases.run("restricted forwarding cannot switch formal domain", [&] {
    refuses(check(finitePrelude + R"(
fn wrapper(a:domain<Fr>,b:domain<Fr>,step:fn(Fr,item:Fr)->Fr effects(stop) where item_from(item, a))->Fr effects(stop){return fold(b,0,step);}
)"),
            "source.scoped-domain");
  });
  cases.run("reconstructed product is not a genuine domain item", [&] {
    refuses(check(finitePrelude + R"(
fn wrapper(rows:domain<(Fr,Fr)>,term:fn(item:(Fr,Fr))->Fr effects(stop) where item_from(item, rows))->Fr effects(stop){return fold(rows,0,fn(s, (a,b))=>s+term((a,b)));}
)"),
            "source.scoped-domain");
  });
  cases.run("retained witness rechecks finite invocation contracts", [&] {
    auto project = take(check(finitePrelude + R"(
fn wrapper(rows:domain<Fr>,step:fn(Fr,item:Fr)->Fr effects(stop) where item_from(item, rows))->Fr effects(stop){return fold(rows,0,step);}
)"));
    // Weakening the selected callee must not authorize a restricted callback.
    auto &fold =
        const_cast<Declaration &>(declarationNamed(project, "m::fold"));
    fold.scopedInputs[0].itemOrigins.clear();
    auto error = checkScopedElaboration(project);
    require(bool(error), "weakened item contract accepted");
    require(toString(std::move(error)).find("source.scoped-witness") !=
                std::string::npos,
            "wrong item contract refusal");
  });
  for (bool valid : {false, true})
    cases.run(valid ? "nested regions retain restricted formal order"
                    : "nested regions refuse fabricated restricted item",
              [&] {
                std::string source =
                    finitePrelude + R"(
fn nested(rows:domain<Fr>,free:fn(Fr)->Fr effects(stop),term:fn(item:Fr)->Fr effects(stop) where item_from(item, rows))->Fr effects(stop){
 return fold(rows,0,fn(state, item)=>{let mut result:Fr=state;
   for j in 0..2 {let value=if true {term()" +
                    std::string(valid ? "item" : "0") +
                    R"()} else {free(item)};result=result+value;}
   result});
}
)";
                if (valid) {
                  auto project = take(check(source));
                  if (auto error = checkScopedElaboration(project))
                    throw std::runtime_error(toString(std::move(error)));
                } else
                  refuses(check(source), "source.scoped-domain");
              });
  for (bool mutateFormal : {false, true})
    cases.run(
        mutateFormal ? "scoped formal parameter mutation refuses"
                     : "scoped invocation target mutation refuses",
        [&] {
          auto project = take(check(finitePrelude + R"(
fn nested(rows:domain<Fr>,free:fn(Fr)->Fr effects(stop),term:fn(item:Fr)->Fr effects(stop) where item_from(item, rows))->Fr effects(stop){
 return fold(rows,0,fn(state, item)=>{let mut result:Fr=state;
   for j in 0..2 {let value=if true {term(item)} else {free(item)};result=result+value;}
   result});
}
)"));
          bool changed = false;
          std::function<void(Body &)> mutate = [&](Body &body) {
            for (auto &op : body.operations) {
              if (auto *invoke = std::get_if<ScopedInvoke>(&op.action);
                  invoke && !changed && invoke->binding == 1) {
                if (mutateFormal)
                  body.scopedBindings[1].parameter = 0;
                else
                  invoke->binding = 0;
                changed = true;
              }
              if (auto *control = std::get_if<LocalControl>(&op.action))
                for (const auto &region : control->regions)
                  mutate(const_cast<Body &>(*region));
            }
            for (auto &binding : body.scopedBindings)
              if (binding.computation)
                mutate(const_cast<Body &>(*binding.computation->body));
          };
          mutate(
              const_cast<Body &>(*declarationNamed(project, "m::nested").body));
          require(changed, "scoped witness mutation target missing");
          auto error = checkScopedElaboration(project);
          require(bool(error), "corrupted scoped invocation accepted");
          require(toString(std::move(error)).find("source.scoped-witness") !=
                      std::string::npos,
                  "wrong scoped identity refusal");
        });
  cases.run("scoped invocation operand order mutation refuses", [&] {
    auto project = take(check(R"(
domain Fr=field("koala-bear");
fn apply(a:Fr,b:Fr,body:fn(Fr,Fr)->Fr effects())->Fr{return body(a,b);}
)"));
    auto &body =
        const_cast<Body &>(*declarationNamed(project, "m::apply").body);
    bool changed = false;
    for (auto &op : body.operations)
      if (auto *invoke = std::get_if<ScopedInvoke>(&op.action)) {
        std::swap(invoke->operands[0], invoke->operands[1]);
        changed = true;
      }
    require(changed, "missing scoped invocation");
    auto error = checkScopedElaboration(project);
    require(bool(error), "scoped operand permutation accepted");
    require(toString(std::move(error)).find("source.scoped-witness") !=
                std::string::npos,
            "wrong invocation operand refusal");
  });
  cases.run("mathematical data preconditions select logical input places", [&] {
    auto project = take(check(R"(
domain Fr=field("koala-bear");


struct Inputs {pub vector:Vector<Fr>,pub matrix:Matrix<Fr>}
pub math fn read(xs:Inputs,i:index,j:index)->bool
 where in_bounds(i,xs.vector),in_bounds(j,xs.matrix,1),equal_extent(xs.vector,xs.matrix,0,0)
 {return true;}
)"));
    const auto &decl = declarationNamed(project, "m::read");
    require(decl.dataPreconditions.size() == 3 &&
                decl.dataPreconditions[0].left.port == 1 &&
                decl.dataPreconditions[0].right.path ==
                    std::vector<unsigned>{0} &&
                decl.dataPreconditions[1].rightAxis == 1,
            "data precondition selectors differ");
    auto inspected = take(inspectDeclarations(project));
    require(inspected.find("index_bound") != std::string::npos &&
                inspected.find("equal_extent") != std::string::npos,
            "declaration inspection lost data conditions");
  });
  for (StringRef source :
       {"fn f(xs:Vector<Fr>,i:index)->bool where in_bounds(i,xs){return true;}",
        "math fn f(xs:Vector<Fr>,i:index)->bool where in_bounds(i,xs,1){return "
        "true;}",
        "math fn f(xs:Vector<Fr>,i:index)->bool where in_bounds(i,ys){return "
        "true;}",
        "math fn f(xs:Vector<Fr>,i:Fr)->bool where in_bounds(i,xs){return "
        "true;}",
        "math fn f(xs:Vector<Fr>,i:index)->bool where "
        "in_bounds(i,xs),in_bounds(i,xs){return true;}"})
    cases.run("invalid data precondition " + source.str(), [&] {
      refuses(check("domain Fr=field(\"koala-bear\");" + source.str()),
              "source.data-bound");
    });
  cases.run("module data conditions may reorder or weaken", [&] {
    take(check(R"(
interface Read<F:Field> {
 math fn read(xs:Vector<F>,ys:Vector<F>,i:index)->F
  where in_bounds(i,xs),equal_extent(xs,ys);
}
module Reader<F:Field>:Read<F> {
 math fn read(left:Vector<F>,right:Vector<F>,j:index)->F
  where equal_extent(left,right),in_bounds(j,left) {
  return intrinsic<Vector<F>>("container.at",right,j);
 }
}
module Constant<F:Field>:Read<F> {
 math fn read(xs:Vector<F>,ys:Vector<F>,i:index)->F {return 0;}
}
)"));
  });
  cases.run("module cannot strengthen data conditions", [&] {
    refuses(check(R"(
interface Read<F:Field> {math fn read(xs:Vector<F>,i:index)->F;}
module Reader<F:Field>:Read<F> {
 math fn read(xs:Vector<F>,i:index)->F where in_bounds(i,xs){return 0;}
}
)"),
            "source.conformance");
  });
  cases.run("declared data bounds compose through ordinary mathematical calls",
            [&] {
              take(check(R"(
domain Fr=field("koala-bear");
math fn at(xs:Vector<Fr>,i:index)->Fr where in_bounds(i,xs) {return intrinsic<Vector<Fr>>("container.at",xs,i);}
math fn forward(xs:Vector<Fr>,ys:Vector<Fr>,i:index)->Fr
 where in_bounds(i,xs),equal_extent(xs,ys) {return at(ys,i);}
)"));
            });
  for (StringRef body : {"return at(xs,i);", "let ignored=at(xs,i);return 0;"})
    cases.run("generic caller must establish data preconditions " + body.str(),
              [&] {
                refuses(check(R"(
domain Fr=field("koala-bear");
math fn at(xs:Vector<Fr>,i:index)->Fr where in_bounds(i,xs) {return intrinsic<Vector<Fr>>("container.at",xs,i);}
math fn invalid(xs:Vector<Fr>,i:index)->Fr {)" +
                              body.str() + "}"),
                        "source.data-bound");
              });
  cases.run("wrong container bound refuses", [&] {
    refuses(check(R"(
domain Fr=field("koala-bear");
math fn invalid(xs:Vector<Fr>,ys:Vector<Fr>,i:index)->Fr where in_bounds(i,xs) {
 return intrinsic<Vector<Fr>>("container.at",ys,i);
})"),
            "source.data-bound");
  });
  const std::string boundPrelude = R"(
domain Fr=field("koala-bear");
math fn total<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item, rows))->S=finite("math.fold");
math fn at(xs:Vector<Fr>,i:index)->Fr where in_bounds(i,xs) {return intrinsic<Vector<Fr>>("container.at",xs,i);}
domain fn paired(xs:Vector<Fr>,ys:Vector<Fr>)->domain<(index,index)>{return zip(indices(xs),indices(ys));}
domain fn coords(xs:Matrix<Fr>)->domain<(index,index)>=domain("matrix.coordinates.row_major");
)";
  for (StringRef source :
       {"math fn work(xs:Vector<Fr>)->Fr{return total(indices(xs),0,fn(state, "
        "i)=>state+at(xs,i));}",
        "math fn work(xs:Vector<Fr>)->Fr{return total(step=fn(state, "
        "i)=>state+at(xs,i),initial=0,rows=indices(xs));}",
        "struct Data {pub xs:Vector<Fr>} math fn work(data:Data)->Fr{return "
        "total(indices(data.xs),0,fn(state, i)=>state+at(data.xs,i));}",
        "math fn work(xs:Vector<Fr>)->Fr{let alias=xs;return "
        "total(indices(xs),0,fn(state, i)=>state+at(alias,i));}",
        "math fn apply(i:index,body:math fn(index)->Fr)->Fr{return "
        "body(i);} math fn work(xs:Vector<Fr>)->Fr{return "
        "total(indices(xs),0,fn(state, "
        "i)=>state+apply(i,fn(unused)=>at(xs,i)));}",
        "math fn work(xs:Matrix<Fr>)->Fr{return total(coords(xs),0,fn(state, "
        "(i,j))=>state+intrinsic<Matrix<Fr>>(\"matrix.at\",xs,i,j));}",
        "math fn work(xs:Vector<Fr>,ys:Vector<Fr>)->Fr where "
        "equal_extent(xs,ys){return total(paired(xs,ys),0,fn(state, "
        "(i,j))=>state+at(xs,i)+at(ys,j));}"})
    cases.run("finite item establishes exact bound " + source.str(), [&] {
      auto project = take(check(boundPrelude + source.str()));
      if (auto error = checkScopedElaboration(project))
        throw std::runtime_error(toString(std::move(error)));
    });
  for (StringRef source :
       {"math fn work(xs:Vector<Fr>,ys:Vector<Fr>)->Fr{return "
        "total(indices(xs),0,fn(state, i)=>state+at(ys,i));}",
        "math fn work(xs:Vector<Fr>,n:index)->Fr{return "
        "total(range(0,n),0,fn(state, i)=>state+at(xs,i));}",
        "math fn work(xs:Matrix<Fr>)->Fr{return total(coords(xs),0,fn(state, "
        "(i,j))=>state+intrinsic<Matrix<Fr>>(\"matrix.at\",xs,j,i));}",
        "math fn apply(i:index,body:math fn(index)->Fr)->Fr{return "
        "body(i);} math fn work(xs:Vector<Fr>)->Fr{return "
        "total(indices(xs),0,fn(state, i)=>state+apply(i,fn(j)=>at(xs,j)));}"})
    cases.run("finite item cannot invent a bound " + source.str(), [&] {
      refuses(check(boundPrelude + source.str()), "source.data-bound");
    });
  cases.run("closed total finite helper discharges extracted bounds", [&] {
    auto project = take(check(boundPrelude + R"(
math fn work(xs:Vector<Fr>,ys:Vector<Fr>)->Fr where equal_extent(xs,ys) {
 return total(indices(xs),0,fn(state, i)=>state+at(ys,i));
}
math fn same(xs:Vector<Fr>)->Fr{return work(xs,xs);}
protocol Demo roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return same(xs);}run Run=Demo;
)"));
    auto closed = take(closeEntry(project, "m::Run"));
    unsigned bounds = 0, extents = 0;
    for (const auto &decl : closed.declarations())
      for (const auto &condition : decl.dataPreconditions)
        if (condition.kind == DataPrecondition::Kind::IndexBound)
          ++bounds;
        else
          ++extents;
    require(bounds && extents, "closure lost data requirements");
    if (auto error = checkScopedSpecialization(closed))
      throw std::runtime_error(toString(std::move(error)));
    for (const auto &decl : closed.declarations())
      if (decl.body && decl.origin && !decl.dataPreconditions.empty()) {
        const_cast<Declaration &>(decl).dataPreconditions.clear();
        break;
      }
    auto error = checkScopedSpecialization(closed);
    require(bool(error), "dropped closed precondition accepted");
    consumeError(std::move(error));
  });
  for (
      const std::string &source : {
          R"(math fn work(xs:Vector<Fr>,ys:Vector<Fr>)->Fr{return total(zip(elements(xs),elements(ys)),0,fn(state, pair)=>state);}
protocol Demo roles(P)(xs:Vector<Fr>@P,ys:Vector<Fr>@P)->(r:Fr@P){return work(xs,ys);}run Run=Demo;)",
          R"(domain fn choose(xs:Vector<Fr>,ys:Vector<Fr>)->domain<Fr>{let unused=zip(elements(xs),elements(ys));return elements(xs);}
math fn work(xs:Vector<Fr>,ys:Vector<Fr>)->Fr{return total(choose(xs,ys),0,fn(state, item)=>state);}
protocol Demo roles(P)(xs:Vector<Fr>@P,ys:Vector<Fr>@P)->(r:Fr@P){return work(xs,ys);}run Run=Demo;)",
          R"(domain fn row(xs:Matrix<Fr>,i:index)->domain<Fr>=domain("matrix.row");
math fn work(xs:Matrix<Fr>,i:index)->Fr{return total(row(xs,i),0,fn(state, item)=>state+item);}
protocol Demo roles(P)(xs:Matrix<Fr>@P,i:index@P)->(r:Fr@P){return work(xs,i);}run Run=Demo;)",
          R"(domain fn array<T:Type+Copy+Drop,N:nat>(xs:[T;N])->domain<T>=domain("source_array");
math fn work(a:Fr)->Fr{let empty:[Fr;0]=[];return total(zip(array(empty),array([a])),0,fn(state, item)=>state);}
protocol Demo roles(P)(a:Fr@P)->(r:Fr@P){return work(a);}run Run=Demo;)",
          R"(type Array<F:Field,N:nat>=builtin("field_array",F,N);
domain fn array<T:Type+Copy+Drop,N:nat>(xs:[T;N])->domain<T>=domain("source_array");
math fn collect<I:Type+Copy+Drop,N:nat>(rows:domain<I>,body:math fn(item:I)->Fr where item_from(item, rows))->Array<Fr,N>=finite("math.collect.field_array");
math fn work(a:Fr)->Array<Fr,3>{return collect(array([a,a]),fn(x)=>x);}
protocol Demo roles(P)(a:Fr@P)->(r:Array<Fr,3>@P){return work(a);}run Run=Demo;)",
      })
    cases.run("total formation is checked before native emission " +
                  source.substr(0, 60),
              [&] {
                auto project = take(check(boundPrelude + source));
                refuses(closeEntry(project, "m::Run"), "source.data-bound");
              });
  cases.run("ordinary Math contracts cannot gain caller-specific assumptions",
            [&] {
              auto project = take(check(boundPrelude + R"(
math fn work(xs:Vector<Fr>,ys:Vector<Fr>)->Fr{
 return total(zip(elements(xs),elements(ys)),0,fn(state, item)=>state);
}
protocol Demo roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return work(xs,xs);}run Run=Demo;
)"));
              refuses(closeEntry(project, "m::Run"), "source.data-bound");
            });
  cases.run("contradictory fixed extent condition refuses", [&] {
    refuses(check(R"(
domain Fr=field("bls12-381.fr");
type Array<F:Field,N:nat>=builtin("field_array",F,N);
math fn bad(xs:Array<Fr,3>,ys:Array<Fr,5>)->bool where equal_extent(xs,ys){return true;}
)"),
            "source.data-bound");
  });
  cases.run("total index literal overflow refuses", [&] {
    refuses(check("math fn bad()->index{return 18446744073709551616;}"),
            "source.literal");
  });
  cases.run("index intrinsic static arguments refuse", [&] {
    refuses(check("math fn bad(a:index,b:index)->bool{return "
                  "intrinsic<1>(\"index.less\",a,b);}"),
            "source.intrinsic");
  });
  cases.run("registered finite definitions retain ordered callback slots", [] {
    auto project = take(check(R"(
fn fold<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,step:fn(S,item:I)->S effects(stop) where item_from(item, rows))->S effects(stop)=finite("local.fold");
fn filtered<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,keep:fn(item:I)->bool effects(stop) where item_from(item, rows),step:fn(S,item:I)->S effects(stop) where item_from(item, rows))->S effects(stop)=finite("local.fold_where");
fn collect<I:Type+Copy+Drop,F:Field>(rows:domain<I>,body:fn(item:I)->F effects(stop) where item_from(item, rows))->Vector<F> effects(stop)=finite("local.collect.vector");
math fn total<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item, rows))->S=finite("math.fold");
)"));
    const auto &fold = declarationNamed(project, "m::fold");
    require(fold.finiteDefinition == "local.fold" && fold.body &&
                fold.body->parameterizedSummary &&
                fold.body->effects.fixed.mayStop,
            "finite definition omitted admission effects");
    const auto &filtered =
        std::get<FiniteApplication>(declarationNamed(project, "m::filtered")
                                        .body->operations.front()
                                        .action);
    require(filtered.body == 1 && filtered.predicate == 0,
            "filtered callback order differs");
    const auto &collect =
        std::get<FiniteApplication>(declarationNamed(project, "m::collect")
                                        .body->operations.front()
                                        .action);
    require(collect.kind == FiniteApplication::Kind::Collect &&
                collect.operands.empty(),
            "collect invented an initial state");
    require(!declarationNamed(project, "m::total").body->effects.fixed.mayStop,
            "total finite definition acquired ordered failure");
  });
  cases.run("finite closure preserves selected helpers and captures", [] {
    auto project = take(check(R"(
domain Fr=field("koala-bear");
fn fold<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,step:fn(S,item:I)->S effects(stop) where item_from(item, rows))->S effects(stop)=finite("local.fold");
fn work(xs:Vector<Fr>,initial:Fr,offset:Fr)->Fr effects(stop){return fold(elements(xs),initial,fn(acc, x)=>acc+x+offset);}
protocol Demo roles(P)(xs:Vector<Fr>@P,initial:Fr@P,offset:Fr@P)->(r:Fr@P){return work(xs,initial,offset);}run Run=Demo;
)"));
    auto closed = take(closeEntry(project, "m::Run"));
    bool found = false;
    for (const auto &decl : closed.declarations())
      if (decl.name == "fold" && decl.body) {
        const auto &finite =
            std::get<FiniteComputation>(decl.body->operations.front().action);
        require(finite.domain && finite.domain->nodes.size() == 1 &&
                    finite.domainOperands.size() == 1 &&
                    finite.operands.size() == 1 &&
                    finite.body.captures.size() == 1 && !finite.predicate,
                "finite closure lost its domain or callback environment");
        found = true;
      }
    require(found, "missing closed fold");
  });
  for (unsigned mutation = 0; mutation < 4; ++mutation)
    cases.run("finite closed witness corruption " + std::to_string(mutation),
              [mutation] {
                auto project = take(check(R"(
domain Fr=field("koala-bear");
fn fold<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,step:fn(S,item:I)->S effects(stop) where item_from(item, rows))->S effects(stop)=finite("local.fold");
protocol Demo roles(P)(xs:Vector<Fr>@P,initial:Fr@P,offset:Fr@P)->(r:Fr@P){return fold(elements(xs),initial,fn(acc, x)=>acc+x+offset);}run Run=Demo;
)"));
                auto closed = take(closeEntry(project, "m::Run"));
                bool changed = false;
                for (const auto &decl : closed.declarations())
                  if (decl.name == "fold" && decl.body) {
                    auto body = std::make_shared<Body>(*decl.body);
                    const_cast<Declaration &>(decl).body = body;
                    auto &finite = std::get<FiniteComputation>(
                        body->operations.front().action);
                    if (mutation == 0)
                      finite.kind = FiniteApplication::Kind::Collect;
                    else if (mutation == 1)
                      finite.body.captures.front() = finite.operands.front();
                    else if (mutation == 2)
                      finite.body.helper = decl.id;
                    else {
                      auto domain =
                          std::make_shared<DomainShape>(*finite.domain);
                      domain->nodes.front().axis = 1;
                      finite.domain = std::move(domain);
                    }
                    changed = true;
                  }
                require(changed, "missing finite mutation target");
                auto error = checkScopedSpecialization(closed);
                require(bool(error), "forged closed finite operation accepted");
                auto message = toString(std::move(error));
                require(message.find(mutation == 3
                                         ? "source.domain-witness"
                                         : "source.scoped-specialization") !=
                            std::string::npos,
                        "wrong finite witness refusal: " + message);
              });
  cases.run("finite Math callback formation retains private captures", [] {
    const std::string definitions = R"(
domain Fr=field("koala-bear");
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item, rows))->S=finite("math.fold");
math fn sum(xs:Vector<Fr>,initial:Fr,offset:Fr)->Fr{return fold(elements(xs),initial,fn(acc, x)=>acc+x+offset);}
)";
    refuses(check(definitions + R"(
protocol Demo roles(P,V)(xs:Vector<Fr>@(P,V),initial:Fr@(P,V),offset:Fr@P)->(r:Fr@(P,V)){return sum(xs,initial,offset);}run Run=Demo;
)"),
            "source.roles");
    auto project = take(check(definitions + R"(
protocol Demo roles(P,V)(xs:Vector<Fr>@(P,V),initial:Fr@(P,V),offset:Fr@P)->(r:Fr@P){return sum(xs,initial,offset);}run Run=Demo;
)"));
    take(closeEntry(project, "m::Run"));
  });
  for (const auto &definition :
       {std::string("fn f<I:Type+Copy+Drop,S:Type>(rows:"
                    "domain<I>,initial:S,step:fn(S,I)->S effects(stop))->S "
                    "effects(stop)=finite(\"local.fold\");"),
        std::string("fn f<I:Type+Copy+Drop,S:Type>(rows:"
                    "domain<I>,initial:S,step:fn(S,item:I)->S effects(stop) "
                    "where item_from(item, rows))->S "
                    "effects(stop)=finite(\"math.fold\");"),
        std::string("fn f<I:Type+Copy+Drop,S:Type>(rows:"
                    "domain<I>,initial:S,step:fn(S,item:I)->S effects(stop) "
                    "where item_from(item, rows))->S "
                    "effects(stop)=finite(\"local.unknown\");")})
    cases.run("finite registered signature refusal " + definition,
              [&] { refuses(check(definition), "source.finite"); });
  cases.run("domain constructors retain a separate static signature", [] {
    auto project = take(check(""));
    const auto &zip = declarationNamed(project, "m::zip");
    require(zip.inputs.empty() && zip.outputs.empty() &&
                zip.domainInputs.size() == 2 && zip.domainResult &&
                zip.domainDefinition && !zip.body,
            "domain signature became a runtime callable");
    const auto &result =
        zip.domainDefinition->bindings[zip.domainDefinition->result];
    require(result.kind == DomainBinding::Kind::Zip &&
                result.children == std::vector<unsigned>({0, 1}),
            "domain order was lost");
    require(take(inspectDeclarations(project)).find("domain_inputs") !=
                std::string::npos,
            "inspection omitted static domains");
  });
  cases.run(
      "mixed group field factory composition and immutable forwarding", [] {
        auto project = take(check(R"(
pub domain fn paired<G:Group>(points:Groups<G>,scalars:Vector<G::Scalar>)->domain<(G,G::Scalar)>{
 let ps=groups(points);let ss=elements(scalars);return zip(ps,ss);
}
pub domain fn forward<T:Type+Copy+Drop>(rows:domain<T>)->domain<T>{return rows;}
)"));
        const auto &paired =
            *declarationNamed(project, "m::paired").domainDefinition;
        require(paired.bindings.size() == 3 && paired.bindings[0].expression &&
                    paired.bindings[1].expression &&
                    paired.bindings[2].expression,
                "composition lost typed constructor applications");
        require(paired.bindings[0].operands[0].index == 0 &&
                    paired.bindings[1].operands[0].index == 1 &&
                    paired.bindings[2].children ==
                        std::vector<unsigned>({0, 1}),
                "composition changed source operand identities");
        require(declarationNamed(project, "m::forward")
                        .domainDefinition->bindings[0]
                        .parameter == 0,
                "forwarding lost the domain parameter");
      });
  cases.run("matrix coordinates source arrays and record sequences", [] {
    take(check(R"(
domain fn row<F:Field>(xs:Matrix<F>,i:index)->domain<F>=domain("matrix.row");
domain fn column<F:Field>(xs:Matrix<F>,i:index)->domain<F>=domain("matrix.column");
domain fn coordinates<F:Field>(xs:Matrix<F>)->domain<(index,index)>=domain("matrix.coordinates.column_major");
domain fn array<T:Type+Copy+Drop,N:nat>(xs:[T;N])->domain<T>=domain("source_array");
struct Row{pub value:index,pub valid:bool}
domain fn rows(xs:Sequence<Row>)->domain<Row>=domain("elements");
)"));
  });
  cases.run("module factory conformance", [] {
    take(check(R"(
interface Domain<F:Field>{domain fn rows(xs:Vector<F>)->domain<F>;}
module All<F:Field>:Domain<F>{domain fn rows(xs:Vector<F>)->domain<F>=domain("elements");}
)"));
  });
  cases.run("ordinary helpers retain domain aliases and forwarding", [] {
    auto project = take(check(R"(
fn ignore<T:Type+Copy+Drop>(rows:domain<T>,fallback:T)->T{return fallback;}
fn forward<T:Type+Copy+Drop>(rows:domain<T>,fallback:T)->T{return ignore(rows,fallback);}
fn example<F:Field>(xs:Vector<F>,fallback:F)->F {
 let rows=elements(xs); let alias=rows;
 return forward(fallback=fallback,rows=alias);
}
)"));
    const auto &body = *declarationNamed(project, "m::example").body;
    require(body.domainBindings.size() == 1 &&
                body.domainBindings.front().expression.has_value(),
            "domain aliases copied or erased their recipe");
    const auto &call = std::get<HelperCall>(body.operations.back().action);
    require(call.domainArguments == std::vector<unsigned>{0},
            "domain call lost recipe identity");
  });
  cases.run("abstract module factory survives typed composition", [] {
    auto project = take(check(R"(
interface Domain<F:Field>{domain fn rows(xs:Vector<F>)->domain<F>;}
domain fn selected<F:Field,C:Domain<F>>(xs:Vector<F>)->domain<(F,F)> {
 let rows=C::rows(xs); return zip(rows,rows);
}
)"));
    const auto &definition =
        *declarationNamed(project, "m::selected").domainDefinition;
    require(definition.bindings[0].kind == DomainBinding::Kind::Application &&
                definition.bindings[0].factory->module.has_value(),
            "abstract factory selection was not retained");
  });
  cases.run("closure preserves factory admission and operand identity", [] {
    auto project = take(check(R"(
domain Fr=field("koala-bear");
domain fn checked<F:Field>(a:Vector<F>,b:Vector<F>)->domain<F> {
 let left=elements(a); let right=elements(b); let unused=zip(left,right); return left;
}
fn example(a:Vector<Fr>,b:Vector<Fr>)->bool {
 let unrelated=zip(elements(a),elements(b));
 let selected=checked(a,b); let shared=checked(a,a);
 return true;
}
)"));
    const auto &body = *declarationNamed(project, "m::example").body;
    std::vector<Declaration> declarations(project.declarations().begin(),
                                          project.declarations().end());
    zkc::language::detail::Work work{Limits{}};
    zkc::language::detail::Semantics types(declarations, project.assets(),
                                           work);
    auto selected = zkc::language::detail::closeDomain(types, declarations,
                                                       body, 3, {}, {});
    require(selected.has_value(),
            types.diagnostic ? types.diagnostic->message : "closure failed");
    require(selected->shape->nodes.size() == 3 &&
                selected->shape->result == 0 &&
                selected->shape->nodes.back().kind == DomainBinding::Kind::Zip,
            "factory admission lost unused zip or included unrelated caller "
            "domain");
    require(selected->shape->inputs.size() == 2,
            "distinct containers became identical");
    auto shared = zkc::language::detail::closeDomain(types, declarations, body,
                                                     4, {}, {});
    require(shared.has_value() && shared->shape->inputs.size() == 1,
            "aliases of one immutable operand were not preserved");
    require(selected->shape->identity != shared->shape->identity,
            "specialization identity erased alias relationships");
  });
  cases.run("closed abstract factory selects module recipe", [] {
    auto project = take(check(R"(
domain Fr=field("koala-bear");
interface Domain<F:Field>{domain fn rows(xs:Vector<F>)->domain<F>;}
module All<F:Field>:Domain<F>{domain fn rows(xs:Vector<F>)->domain<F>=domain("elements");}
domain fn selected<F:Field,C:Domain<F>>(xs:Vector<F>)->domain<F>{return C::rows(xs);}
fn example(xs:Vector<Fr>)->bool {let rows=selected<Fr,All<Fr>>(xs);return true;}
)"));
    const auto &body = *declarationNamed(project, "m::example").body;
    std::vector<Declaration> declarations(project.declarations().begin(),
                                          project.declarations().end());
    zkc::language::detail::Work work{Limits{}};
    zkc::language::detail::Semantics types(declarations, project.assets(),
                                           work);
    auto selected = zkc::language::detail::closeDomain(types, declarations,
                                                       body, 0, {}, {});
    require(selected.has_value(),
            types.diagnostic ? types.diagnostic->message : "closure failed");
    require(selected->shape->nodes.size() == 1 &&
                selected->shape->nodes[0].kind == DomainBinding::Kind::Elements,
            "module factory did not close to its selected constructor");
  });
  cases.run("named factory arguments preserve child admission order", [] {
    auto project = take(check(R"(
fn example(a:index,b:index,c:index,d:index)->bool {
 let rows=zip(b=range(c,d),a=range(a,b)); return true;
}
)"));
    const auto &body = *declarationNamed(project, "m::example").body;
    std::vector<Declaration> declarations(project.declarations().begin(),
                                          project.declarations().end());
    zkc::language::detail::Work work{Limits{}};
    zkc::language::detail::Semantics types(declarations, project.assets(),
                                           work);
    auto selected = zkc::language::detail::closeDomain(types, declarations,
                                                       body, 2, {}, {});
    require(selected.has_value(),
            types.diagnostic ? types.diagnostic->message : "closure failed");
    require(
        selected->operands[0].index == 2 && selected->operands[1].index == 3 &&
            selected->shape->nodes[2].children == std::vector<unsigned>({1, 0}),
        "named mapping reordered constructor admission or item positions");
  });
  cases.run("scoped and control regions capture static domains", [] {
    auto project = take(check(R"(
fn ignore<T:Type+Copy+Drop>(rows:domain<T>,fallback:T)->T{return fallback;}
fn apply<T:Type+Copy+Drop>(x:T,body:fn(T)->T effects(stop))->T effects(stop){return body(x);}
fn example<F:Field>(xs:Vector<F>,x:F,choose:bool)->F {
 let rows=elements(xs);
 return apply(x,fn(y)=>if choose {ignore(rows,y)} else {y});
}
)"));
    const auto &body = *declarationNamed(project, "m::example").body;
    const auto &binding = body.scopedBindings.front();
    require(binding.domainCaptures == std::vector<unsigned>{0} &&
                binding.computation->domainCaptures.size() == 1,
            "callback lost captured domain identity");
    require(binding.computation->body->domainBindings.front().parameter == 0,
            "captured domain became a data parameter");
  });
  cases.run(
      "domain dependencies survive generic helper and callback forwarding", [] {
        auto project = take(check(R"(
interface Inspect<F:Field>{math fn inspect(rows:domain<F>,fallback:F)->F;}
math fn inner<F:Field,C:Inspect<F>>(rows:domain<F>,fallback:F)->F {
 return C::inspect(rows,fallback);
}
math fn outer<F:Field,C:Inspect<F>>(rows:domain<F>,fallback:F)->F {
 return inner<F,C>(rows,fallback);
}
math fn apply<F:Field>(x:F,body:math fn(F)->F effects())->F{return body(x);}
math fn captured<F:Field,C:Inspect<F>>(rows:domain<F>,fallback:F)->F {
 return apply(fallback,fn(x)=>inner<F,C>(rows,x));
}
)"));
        std::vector<Declaration> declarations(project.declarations().begin(),
                                              project.declarations().end());
        zkc::language::detail::Work work{Limits{}};
        zkc::language::detail::Semantics types(declarations, project.assets(),
                                               work);
        for (auto name : {"m::outer", "m::captured"}) {
          const auto &body = *declarationNamed(project, name).body;
          require(body.parameterizedSummary,
                  "unknown domain was cached as a constant dependency");
          auto summary = zkc::language::detail::summarizeBody(
              types, declarations, body, {}, {{{7}, false}}, {}, 1,
              {{{3}, false}});
          require(summary.has_value(), types.diagnostic
                                           ? types.diagnostic->message
                                           : "missing summary");
          require(
              summary->results.front().inputs == std::vector<unsigned>({3, 7}),
              "domain operand dependency was lost through generic forwarding");
          require(summary->parameterized,
                  "abstract domain consumer appeared concrete");
        }
      });
  cases.run(
      "closure input layout preserves aliases without merging distinct "
      "containers",
      [] {
        auto project = take(check(R"(
domain Fr=field("koala-bear");
struct Pair{pub left:Vector<Fr>,pub right:Vector<Fr>}
fn example(xs:Pair,other:Vector<Fr>)->(Vector<Fr>,Vector<Fr>,Vector<Fr>){
 return (xs.left,xs.left,xs.right);
}
)"));
        auto body = *declarationNamed(project, "m::example").body;
        std::vector<ValueId> projected;
        for (const auto &op : body.operations)
          if (std::holds_alternative<Projection>(op.action))
            projected.push_back(op.results.front());
        if (projected.size() == 2) {
          auto duplicate = body.operations.front();
          ValueId fresh{uint32_t(body.values.size())};
          body.values.push_back(body.values[projected.front().index]);
          duplicate.results = {fresh};
          body.operations.push_back(std::move(duplicate));
          projected.insert(projected.begin() + 1, fresh);
        }
        require(projected.size() == 3, "missing authored projections");
        std::vector<Declaration> declarations(project.declarations().begin(),
                                              project.declarations().end());
        zkc::language::detail::Work work{Limits{}};
        zkc::language::detail::Semantics types(declarations, project.assets(),
                                               work);
        auto result = zkc::language::detail::closeInputs(
            types, body, {projected[0], projected[1], ValueId{1}},
            {projected[1], projected[2], ValueId{1}, projected[2]}, {});
        require(result.has_value(), types.diagnostic ? types.diagnostic->message
                                                     : "missing layout");
        require(result->layout.inputs == std::vector<unsigned>({0, 0, 2}) &&
                    result->layout.captures ==
                        std::vector<unsigned>({0, 3, 2, 3}) &&
                    result->operands.size() == 4,
                "joint layout lost a projection alias or merged distinct "
                "containers");
        auto callback = zkc::language::detail::closeInputs(
            types, body, {std::nullopt, projected[0]},
            {projected[1], projected[2]}, {});
        require(callback &&
                    callback->layout.inputs == std::vector<unsigned>({0, 1}) &&
                    callback->layout.captures == std::vector<unsigned>({1, 2}),
                "unknown callback parameter interfered with capture identity");
        Body corrupt = body;
        auto &projection =
            std::get<Projection>(corrupt.operations.front().action);
        projection.input = corrupt.operations.front().results.front();
        zkc::language::detail::ValueOrigins origins(types, corrupt);
        require(!origins.get(projection.input),
                "cyclic projection origin was accepted");
      });
  cases.run(
      "shared factory expansion stays bounded across forty forwarding levels",
      [] {
        std::string source = "domain fn layer0(a:index,b:index)->"
                             "domain<index>{return range(a,b);}";
        for (unsigned i = 1; i <= 40; ++i) {
          auto previous = "layer" + std::to_string(i - 1);
          source += "domain fn layer" + std::to_string(i) +
                    "(a:index,b:index)->domain<index>{let unused=" + previous +
                    "(a,b);return " + previous + "(a,b);}";
        }
        source += "fn example(a:index,b:index)->index{let "
                  "rows=layer40(a,b);return a;}";
        auto project = take(check(source));
        const auto &body = *declarationNamed(project, "m::example").body;
        std::vector<Declaration> declarations(project.declarations().begin(),
                                              project.declarations().end());
        zkc::language::detail::Work work{Limits{}};
        zkc::language::detail::Semantics types(declarations, project.assets(),
                                               work);
        auto result = zkc::language::detail::closeDomain(types, declarations,
                                                         body, 0, {}, {});
        require(result.has_value(), types.diagnostic ? types.diagnostic->message
                                                     : "missing closed domain");
        require(result->shape->nodes.size() == 1 &&
                    result->shape->inputs.size() == 2,
                "shared factory graph expanded repeated selected recipes");
        require(zkc::language::detail::checkDomainClosure(
                    types, declarations, body, 0, {}, {}, *result),
                types.diagnostic ? types.diagnostic->message
                                 : "shared factory witness failed");
      });
  cases.run(
      "inherited domain inputs and descriptor size are checked at closure", [] {
        auto project = take(check("fn forward(a:index,b:index,rows:"
                                  "domain<index>)->index{return a;}"));
        const auto &body = *declarationNamed(project, "m::forward").body;
        std::vector<Declaration> declarations(project.declarations().begin(),
                                              project.declarations().end());
        for (unsigned mutation = 0; mutation < 3; ++mutation) {
          auto shape = std::make_shared<DomainShape>();
          shape->inputs = {Type(Type::Kind::Index), Type(Type::Kind::Index)};
          shape->nodes.push_back({DomainBinding::Kind::Range,
                                  Type(Type::Kind::Index),
                                  {{0}, {1}},
                                  {}});
          shape->result = 0;
          if (mutation == 1)
            shape->inputs.front() = Type{};
          if (mutation == 2)
            shape->nodes.resize(4096, shape->nodes.front());
          zkc::language::detail::Work work{Limits{}};
          zkc::language::detail::Semantics types(declarations, project.assets(),
                                                 work);
          auto result = zkc::language::detail::closeDomain(
              types, declarations, body, 0, {}, {{shape, {{0}, {1}}}});
          if (mutation == 0)
            require(result.has_value(), types.diagnostic
                                            ? types.diagnostic->message
                                            : "valid inherited shape refused");
          else {
            require(!result && types.diagnostic,
                    "invalid inherited descriptor accepted");
            require(
                types.diagnostic->code ==
                    (mutation == 1 ? "source.finite-domain" : "source.limit"),
                "wrong inherited descriptor refusal");
          }
        }
      });
  cases.run(
      "domain call occurrence identity is checked independently of its span",
      [] {
        auto project = take(check(R"(
fn ignore(rows:domain<index>,fallback:index)->index{return fallback;}
fn example(a:index,b:index)->index{return ignore(range(a,b),a);}
)"));
        auto &decl =
            const_cast<Declaration &>(declarationNamed(project, "m::example"));
        auto body = std::make_shared<Body>(*decl.body);
        decl.body = body;
        ++*body->domainBindings.front().expression;
        auto error = checkScopedElaboration(project);
        require(bool(error), "changed domain expression identity was accepted");
        require(toString(std::move(error)).find("source.scoped-witness") !=
                    std::string::npos,
                "wrong source occurrence refusal");
      });
  cases.run(
      "descriptor witness checks admission and operand mappings without its "
      "key",
      [] {
        auto project = take(check(R"(
domain fn prepared(a:index,b:index,c:index,d:index)->domain<index>{
 let checked=zip(range(a,b),range(c,d));return range(a,b);
}
fn example(a:index,b:index,c:index,d:index)->index{let rows=prepared(a,b,c,d);return a;}
)"));
        const auto &body = *declarationNamed(project, "m::example").body;
        std::vector<Declaration> declarations(project.declarations().begin(),
                                              project.declarations().end());
        zkc::language::detail::Work work{Limits{}};
        zkc::language::detail::Semantics types(declarations, project.assets(),
                                               work);
        auto original = zkc::language::detail::closeDomain(types, declarations,
                                                           body, 0, {}, {});
        require(original.has_value(), types.diagnostic
                                          ? types.diagnostic->message
                                          : "closure failed");
        require(original->shape->nodes.size() == 3 &&
                    original->shape->result == 0,
                "missing retained check-only zip");
        Body caller = body;
        caller.values.insert(caller.values.begin(), body.values.front());
        ++caller.inputs;
        auto shifted = [](ValueId value) { return ValueId{value.index + 1}; };
        zkc::language::detail::mapBodyValues(caller, shifted);
        auto inputs = zkc::language::detail::bindDomainInputs(
            types, declarations, body, caller, shifted, 0, {}, {},
            *original->shape);
        require(inputs && inputs->size() == original->operands.size(),
                "mapped descriptor witness failed");
        for (unsigned i = 0; i < inputs->size(); ++i)
          require((*inputs)[i].index == original->operands[i].index + 1,
                  "domain witness confused template and caller SSA spaces");
        for (unsigned mutation = 0; mutation < 9; ++mutation) {
          auto candidate = *original;
          auto shape = std::make_shared<DomainShape>(*candidate.shape);
          candidate.shape = shape;
          shape->identity = "untrusted producer key";
          if (mutation == 1)
            shape->nodes.pop_back();
          if (mutation == 2)
            std::swap(shape->nodes[0], shape->nodes[1]);
          if (mutation == 3)
            std::swap(candidate.operands[0], candidate.operands[2]);
          if (mutation == 4)
            std::swap(shape->nodes[0].operands[0], shape->nodes[0].operands[1]);
          if (mutation == 5)
            shape->result = 1;
          if (mutation == 6)
            shape->nodes.push_back(shape->nodes.front());
          if (mutation == 7)
            shape->inputs.front() = Type{};
          if (mutation == 8)
            shape->nodes.front().expression = 7;
          zkc::language::detail::Work witnessWork{Limits{}};
          zkc::language::detail::Semantics witness(
              declarations, project.assets(), witnessWork);
          bool valid = zkc::language::detail::checkDomainClosure(
              witness, declarations, body, 0, {}, {}, candidate);
          if (mutation == 0)
            require(valid, witness.diagnostic ? witness.diagnostic->message
                                              : "valid descriptor refused");
          else
            require(!valid && witness.diagnostic &&
                        witness.diagnostic->code == "source.domain-witness",
                    "corrupt descriptor accepted or refused for the wrong "
                    "reason: " +
                        std::to_string(mutation));
        }
      });
  const std::vector<std::pair<std::string, std::string>> invalid = {
      {R"(domain fn bad(x:index)->domain<index>=domain("unknown");)",
       "source.finite-domain"},
      {R"(domain fn bad(x:index)->domain<index>=domain("elements");)",
       "source.finite-domain"},
      {R"(domain fn bad(a:index,b:bool)->domain<index>=domain("range");)",
       "source.finite-domain"},
      {R"(domain fn bad<F:Field>(xs:Vector<F>)->domain<index>=domain("indices.columns");)",
       "source.finite-domain"},
      {R"(domain fn bad<A:Type+Copy+Drop,B:Type+Copy+Drop>(a:domain<A>,b:domain<B>)->domain<(B,A)>=domain("zip");)",
       "source.finite-domain"},
      {R"(domain fn bad<T:Type>(a:domain<T>)->domain<T> where (){return a;})",
       "source.finite-domain"},
      {R"(domain fn bad(lo:index,hi:index)->domain<index>{let mut rows=range(lo,hi);return rows;})",
       "source.finite-domain"},
      {R"(domain fn bad(lo:index,hi:index)->domain<index>{return bad(lo,hi);})",
       "source.cycle"},
      {R"(protocol Bad roles(P)(rows:domain<index>@P)->(){return();})",
       "source.scoped"},
      {R"(interface Bad{fn work(rows:domain<index>,body:fn(item:bool)->bool effects() where item_from(item, rows))->bool effects(stop, opaque);})",
       "source.finite-domain"},
  };
  for (unsigned i = 0; i < invalid.size(); ++i)
    cases.run("refuse invalid finite domain " + std::to_string(i), [&, i] {
      auto result = check(invalid[i].first);
      require(!result, "invalid domain accepted");
      require(toString(result.takeError()).find(invalid[i].second) !=
                  std::string::npos,
              "wrong domain refusal diagnostic");
    });
  cases.run("domains close through ordinary generic helper forwarding", [] {
    auto project = take(check(R"(
domain Fr=field("koala-bear");
fn ignore<T:Type+Copy+Drop>(rows:domain<T>,fallback:T)->T{return fallback;}
fn forward<T:Type+Copy+Drop>(rows:domain<T>,fallback:T)->T{return ignore(rows,fallback);}
protocol Demo roles(P)(xs:Vector<Fr>@P,fallback:Fr@P)->(r:Fr@P){return forward(elements(xs),fallback);}run Run=Demo;
)"));
    auto closed = take(closeEntry(project, "m::Run"));
    unsigned forwarded = 0;
    for (const auto &decl : closed.declarations())
      if (decl.body) {
        require(decl.domainInputs.empty() && decl.body->domainBindings.empty(),
                "static domain survived in runtime signature");
        if (decl.name == "forward" || decl.name == "ignore") {
          require(decl.domainArguments.size() == 1 && decl.inputs.size() == 2 &&
                      decl.closureLayout.captures == std::vector<unsigned>{1},
                  "domain operand did not become an explicit helper input");
          ++forwarded;
        }
      }
    require(forwarded == 2, "forwarding helper missing");
  });
  cases.run("domain and callback captures share authored SSA identities", [] {
    auto project = take(check(R"(
domain Fr=field("koala-bear");
fn observe(rows:domain<index>,xs:Vector<Fr>,body:fn(Vector<Fr>)->Vector<Fr> effects())->Vector<Fr>{return body(xs);}
protocol Demo roles(P)(xs:Vector<Fr>@P)->(r:Vector<Fr>@P){return observe(indices(xs),xs,fn(_)=>xs);}run Run=Demo;
)"));
    auto closed = take(closeEntry(project, "m::Run"));
    bool found = false;
    for (const auto &decl : closed.declarations())
      if (decl.body && decl.name == "observe") {
        require(decl.inputs.size() == 1 && decl.closureLayout.captures ==
                                               std::vector<unsigned>({0, 0}),
                "domain and callback capture received independent ports");
        found = true;
      }
    require(found, "missing joint helper");
  });
  cases.run("callbacks capture domains and retain ordinary forwarding", [] {
    auto project = take(check(R"(
domain Fr=field("koala-bear");
fn ignore<T:Type+Copy+Drop>(rows:domain<T>,fallback:T)->T{return fallback;}
fn apply(x:Fr,body:fn(Fr)->Fr effects())->Fr{return body(x);}
fn outer(xs:Vector<Fr>,x:Fr)->Fr{let rows=elements(xs);return apply(x,fn(y)=>ignore(rows,y));}
protocol Demo roles(P)(xs:Vector<Fr>@P,x:Fr@P)->(r:Fr@P){return outer(xs,x);}run Run=Demo;
)"));
    auto closed = take(closeEntry(project, "m::Run"));
    bool found = false;
    for (const auto &decl : closed.declarations())
      if (decl.body && decl.scopedOrigin) {
        require(decl.domainArguments.size() == 1 && decl.inputs.size() == 2,
                "callback lost static captured domain");
        found = true;
      }
    require(found, "missing callback");
  });
  cases.run("closed domains survive local conditional and loop regions", [] {
    auto project = take(check(R"(
domain Fr=field("koala-bear");
fn ignore(rows:domain<Fr>,fallback:Fr)->Fr{return fallback;}
fn outer(xs:Vector<Fr>,x:Fr,n:index,flag:bool)->Fr{
 let rows=elements(xs);let mut result=x;
 for i in 0..n { result=if flag {ignore(rows,result)} else {result}; }
 return result;
}
protocol Demo roles(P)(xs:Vector<Fr>@P,x:Fr@P,n:index@P,flag:bool@P)->(r:Fr@P){return outer(xs,x,n,flag);}run Run=Demo;
)"));
    take(closeEntry(project, "m::Run"));
  });
  for (unsigned mutation = 0; mutation < 3; ++mutation)
    cases.run("closed domain edge mutation " + std::to_string(mutation), [&] {
      auto project = take(check(R"(
domain Fr=field("koala-bear");
fn ignore(rows:domain<index>,fallback:Fr)->Fr{return fallback;}
protocol Demo roles(P)(a:index@P,b:index@P,x:Fr@P)->(r:Fr@P){return ignore(range(a,b),x);}run Run=Demo;
)"));
      auto closed = take(closeEntry(project, "m::Run"));
      for (const auto &decl : closed.declarations())
        if (decl.body && decl.name == "ignore") {
          auto &candidate = const_cast<Declaration &>(decl);
          if (mutation == 2)
            candidate.closureLayout.captures[1] =
                candidate.closureLayout.captures[0];
          else {
            auto shape = std::make_shared<DomainShape>(
                *candidate.domainArguments.front());
            candidate.domainArguments.front() = shape;
            if (mutation == 0)
              std::swap(shape->nodes.back().operands[0],
                        shape->nodes.back().operands[1]);
            else
              shape->nodes.clear();
          }
        }
      auto error = checkScopedSpecialization(closed);
      require(bool(error), "forged domain specialization accepted");
      auto message = toString(std::move(error));
      require(message.find("source.domain-witness") != std::string::npos ||
                  message.find("source.closure-inputs") != std::string::npos ||
                  message.find("source.scoped-specialization") !=
                      std::string::npos,
              "wrong domain specialization refusal");
    });
  cases.run(
      "protocol repetition captures recipe operands at their participants", [] {
        auto project = take(check(R"(
domain Fr=field("koala-bear");
fn ignore(rows:domain<Fr>,fallback:Fr)->Fr{return fallback;}
protocol Demo roles(P,V)(xs:Vector<Fr>@P,x:Fr@P,n:index@(P,V))->(r:Fr@P){
 let rows=elements(xs);let mut result@P=x;
 for _ in 0..n roles(P,V) max 4 {
   for _ in 0..n roles(P,V) max 4 {result=ignore(rows,result+x);}
 }
 return result;
}run Run=Demo;
)"));
        take(closeEntry(project, "m::Run"));
      });
  cases.run("domain capture cannot introduce an absent protocol participant",
            [] {
              refuses(check(R"(
domain Fr=field("koala-bear");
fn ignore(rows:domain<Fr>,fallback:Fr)->Fr{return fallback;}
protocol Demo roles(P,V)(xs:Vector<Fr>@V,x:Fr@P,n:index@P)->(r:Fr@P){
 let rows=elements(xs);let mut result@P=x;
 for _ in 0..n roles(P) max 4 {result=ignore(rows,result);}
 return result;
}run Run=Demo;
)"),
                      "source.roles");
            });
  cases.run("domain operand availability participates in nested call placement",
            [] {
              refuses(check(R"(
domain Fr=field("koala-bear");
fn ignore(rows:domain<Fr>,fallback:Fr)->Fr{return fallback;}
protocol Demo roles(P,V)(xs:Vector<Fr>@V,x:Fr@P,n:index@(P,V))->(r:Fr@P){
 let rows=elements(xs);let mut result@P=x;
 for _ in 0..n roles(P,V) max 4 {result=ignore(rows,result);}
 return result;
}run Run=Demo;
)"),
                      "source.roles");
            });
  return cases.result();
}
