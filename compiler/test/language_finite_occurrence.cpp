#include "../lib/Language/FiniteContracts.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Translation/Language.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace source_detail = zkc::language::detail;
namespace {
const std::string prelude = R"(module m;
domain Fr=field("koala-bear");
type Vector<F:Field>=builtin("vector",F);
type Array<F:Field,N:nat>=builtin("field_array",F,N);
domain fn elements<F:Field>(xs:Vector<F>)->domain<F>=domain("elements");
domain fn fixed_elements<F:Field,N:nat>(xs:Array<F,N>)->domain<F>=domain("elements");
domain fn indices<F:Field>(xs:Vector<F>)->domain<index>=domain("indices");
domain fn array<T:Type+Copy+Drop,N:nat>(xs:[T;N])->domain<T>=domain("source_array");
domain fn range(lo:index,hi:index)->domain<index>=domain("range");
domain fn product<A:Type+Copy+Drop,B:Type+Copy+Drop>(a:domain<A>,b:domain<B>)->domain<(A,B)>=domain("product");
domain fn zip<A:Type+Copy+Drop,B:Type+Copy+Drop>(a:domain<A>,b:domain<B>)->domain<(A,B)>=domain("zip");
math fn fixed<I:Type+Copy+Drop,N:nat>(rows:domain<I>,body:math fn(item:I)->Fr where item_from(item,rows))->Array<Fr,N>=finite("math.collect.field_array");
math fn mapped<I:Type+Copy+Drop>(rows:domain<I>,body:math fn(item:I)->Fr where item_from(item,rows))->Vector<Fr>=finite("math.collect.vector");
math fn filtered<I:Type+Copy+Drop>(rows:domain<I>,keep:math fn(item:I)->bool where item_from(item,rows),body:math fn(item:I)->Fr where item_from(item,rows))->Vector<Fr>=finite("math.collect.vector_where");
math fn total<I:Type+Copy+Drop>(rows:domain<I>,initial:Fr,step:math fn(Fr,item:I)->Fr where item_from(item,rows))->Fr=finite("math.fold");
math fn index_id(i:index)->index{return i;}
math fn vector_id(xs:Vector<Fr>)->Vector<Fr>{return xs;}
math fn at(xs:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){return intrinsic<Vector<Fr>>("container.at",xs,i);}
)";
Expected<CheckedProject> check(StringRef source) {
  auto captured = capture({{"m", prelude + source.str(), "occurrence.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
Expected<ClosedEntry> close(StringRef source) {
  auto project = check(source);
  if (!project)
    return project.takeError();
  return closeEntry(*project, "m::Run");
}
void verify(const ClosedEntry &closed, mlir::MLIRContext &context) {
  if (auto error = checkScopedSpecialization(closed))
    throw std::runtime_error(toString(std::move(error)));
  auto bytes = take(emitOriginal(closed, context));
  auto module = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
  require(bool(module) && succeeded(mlir::verify(*module)),
          "finite occurrence original did not verify");
  take(compareOriginal(closed, *module));
}
void requireAdmitted(const ClosedEntry &closed, const Declaration &declaration,
                     const Body &body) {
  std::vector<Declaration> declarations(closed.declarations().begin(),
                                        closed.declarations().end());
  Limits limits;
  source_detail::Work work{limits};
  source_detail::Semantics types(declarations, closed.project().assets(), work);
  if (!source_detail::checkFiniteContracts(types, declarations, declaration,
                                           body))
    throw std::runtime_error(toString(types.takeError()));
}
std::string fixedSubject(StringRef domain, unsigned size) {
  return "math fn subject(a:Fr)->Array<Fr," + std::to_string(size) +
         ">{return fixed(" + domain.str() +
         ",fn(item)=>a);}\n"
         "protocol Demo roles(P)(a:Fr@P)->(r:Array<Fr," +
         std::to_string(size) + ">@P){return subject(a);}run Run=Demo;";
}
} // namespace
int main() {
  Cases cases;
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  for (const auto &sample : std::vector<std::pair<std::string, unsigned>>{
           {"range(0,4)", 4},
           {"range(index_id(0),index_id(4))", 4},
           {"range(4,1)", 0},
           {"range(2,2)", 0},
           {"product(range(0,2),range(1,4))", 6},
           {"product(range(4,1),range(0,3))", 0},
           {"zip(range(0,4),range(1,5))", 4},
           {"array([a,a,a,a])", 4}})
    cases.run("actual finite cardinality " + sample.first, [&] {
      auto closed = take(close(fixedSubject(sample.first, sample.second)));
      unsigned occurrences = 0, callbackInstances = 0;
      for (const auto &declaration : closed.declarations()) {
        if (declaration.body && declaration.name == "subject")
          for (const auto &op : declaration.body->operations)
            occurrences += std::holds_alternative<FiniteComputation>(op.action);
        if (declaration.body && declaration.scopedOrigin)
          ++callbackInstances;
        require(!declaration.body || declaration.name != "fixed",
                "direct finite definition became a generic helper instance");
      }
      require(occurrences == 1 && callbackInstances,
              "finite occurrence or separate callback instance missing");
      verify(closed, context);
    });
  cases.run("unused incompatible fixed collect fails during source checking",
            [] {
              refuses(check(R"(
math fn unused(xs:Array<Fr,5>)->Array<Fr,4>{return fixed(fixed_elements(xs),fn(x)=>x);}
protocol Demo roles(P)(a:Fr@P)->(r:Fr@P){return a;}run Run=Demo;
)"),
                      "source.data-bound");
            });
  cases.run("unknown fixed collect supplies no bound on its dynamic source",
            [] {
              refuses(check(R"(
math fn subject(xs:Vector<Fr>)->Fr{let ys:Array<Fr,4>=fixed(elements(xs),fn(x)=>x);return at(xs,3);}
)"),
                      "source.data-bound");
            });
  cases.run("unknown fixed collect retains its generic formation obligation",
            [] {
              const auto source = R"(
math fn subject(xs:Vector<Fr>)->Array<Fr,4>{return fixed(elements(xs),fn(x)=>x);}
protocol Demo roles(P)(xs:Vector<Fr>@P)->(r:Array<Fr,4>@P){return subject(xs);}run Run=Demo;
)";
              auto project = take(check(source));
              refuses(closeEntry(project, "m::Run"), "source.data-bound");
            });
  cases.run("symbolic fixed result supplies no numeric count before formation",
            [] {
              refuses(check(R"(
math fn subject<N:nat>(xs:Array<Fr,5>)->Fr{let ys:Array<Fr,N>=fixed(fixed_elements(xs),fn(x)=>x);let zs=mapped(fixed_elements(ys),fn(x)=>x);return at(zs,4);}
)"),
                      "source.data-bound");
            });
  for (unsigned size : {4u, 5u})
    cases.run("symbolic fixed formation closes at " + std::to_string(size),
              [&] {
                auto project = take(check(
                    R"(
math fn subject<N:nat>(xs:Array<Fr,5>)->Array<Fr,N>{return fixed(fixed_elements(xs),fn(x)=>x);}
math fn work<N:nat>(a:Fr)->Array<Fr,N>{let xs:Array<Fr,5>=fixed(range(0,5),fn(i)=>a);return subject<N>(xs);}
protocol Demo roles(P)(a:Fr@P)->(r:Array<Fr,)" +
                    std::to_string(size) + ">@P){return work<" +
                    std::to_string(size) + ">(a);}run Run=Demo;"));
                if (size == 5)
                  verify(take(closeEntry(project, "m::Run")), context);
                else
                  refuses(closeEntry(project, "m::Run"), "source.data-bound");
              });
  cases.run("generic finite signatures preserve input and result substitution",
            [&] {
              verify(take(close(R"(
math fn seeded<F:Field,I:Type+Copy+Drop>(rows:domain<I>,initial:F,step:math fn(F,item:I)->F where item_from(item,rows))->F=finite("math.fold");
math fn subject<N:nat>(xs:Array<Fr,N>,seed:Fr)->Fr{return seeded(fixed_elements(xs),seed,fn(s,x)=>s+x);}
math fn work(a:Fr,seed:Fr)->Fr{let xs:Array<Fr,4>=fixed(range(0,4),fn(i)=>a);return subject(xs,seed);}
protocol Demo roles(P)(a:Fr@P,seed:Fr@P)->(r:Fr@P){return work(a,seed);}run Run=Demo;
)")),
                     context);
            });
  for (unsigned size : {0u, 1u})
    cases.run("finite static natural requirement at " + std::to_string(size),
              [&] {
                auto source =
                    R"(
math fn bounded<N:nat>(rows:domain<Fr>,initial:Fr,step:math fn(Fr,item:Fr)->Fr where item_from(item,rows))->Fr where 1<=N=finite("math.fold");
math fn subject(xs:Vector<Fr>)->Fr{return bounded<)" +
                    std::to_string(size) + R"(>(elements(xs),0,fn(s,x)=>s+x);}
protocol Demo roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return subject(xs);}run Run=Demo;
)";
                if (size)
                  verify(take(close(source)), context);
                else
                  refuses(check(source), "source.bound");
              });
  cases.run("selected module finite definition substitutes its field", [&] {
    verify(take(close(R"(
interface Folder<F:Field>{math fn fold(rows:domain<F>,initial:F,step:math fn(F,item:F)->F where item_from(item,rows))->F;}
module Ordered<F:Field>:Folder<F>{math fn fold(rows:domain<F>,initial:F,step:math fn(F,item:F)->F where item_from(item,rows))->F=finite("math.fold");}
math fn selected<F:Field,C:Folder<F>>(xs:Vector<F>,seed:F)->F{return C::fold(elements(xs),seed,fn(s,x)=>s+x);}
protocol Demo roles(P)(xs:Vector<Fr>@P,seed:Fr@P)->(r:Fr@P){return selected<Fr,Ordered<Fr>>(xs,seed);}run Run=Demo;
)")),
           context);
  });
  cases.run("mapped bound transfers actual container extent", [&] {
    auto closed = take(close(R"(
math fn subject(xs:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){let ys=mapped(elements(vector_id(xs)),fn(x)=>x);return at(ys,i);}
math fn work(xs:Vector<Fr>)->Fr{return total(indices(xs),0,fn(s,i)=>s+subject(xs,i));}
protocol Demo roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return work(xs);}run Run=Demo;
)"));
    verify(closed, context);
  });
  cases.run("column projection conditions justify collection-derived zip", [&] {
    verify(take(close(R"(
struct Columns{pub counts:Vector<Fr>,pub reciprocals:Vector<Fr>}
math fn weighted(counts:Vector<Fr>,reciprocals:Vector<Fr>)->Fr where equal_extent(counts,reciprocals){let collected=mapped(elements(reciprocals),fn(x)=>x);return total(zip(elements(counts),elements(collected)),0,fn(s,p)=>s+p.0*p.1);}
math fn columns(t:Columns)->Fr where equal_extent(t.counts,t.reciprocals){return weighted(t.counts,t.reciprocals);}
math fn subject(t:Columns)->Fr{let collected=mapped(elements(t.reciprocals),fn(x)=>x);return weighted(t.reciprocals,collected);}
protocol Demo roles(P)(t:Columns@P)->(r:Fr@P){return subject(t);}run Run=Demo;
)")),
           context);
  });
  cases.run("different columns cannot justify collection-derived total zip",
            [] {
              refuses(close(R"(
struct Columns{pub counts:Vector<Fr>,pub reciprocals:Vector<Fr>}
math fn subject(t:Columns)->Fr{let collected=mapped(elements(t.reciprocals),fn(x)=>x);return total(zip(elements(t.counts),elements(collected)),0,fn(s,p)=>s+p.0*p.1);}
protocol Demo roles(P)(t:Columns@P)->(r:Fr@P){return subject(t);}run Run=Demo;
)"),
                      "source.data-bound");
            });
  cases.run("source and closed collections publish fresh numeric extents", [&] {
    verify(take(close(R"(
math fn subject(a:Fr)->Array<Fr,4>{let xs=mapped(range(index_id(0),index_id(4)),fn(i)=>a);let ys=mapped(xs,fn(x)=>x);return fixed(ys,fn(x)=>x);}
protocol Demo roles(P)(a:Fr@P)->(r:Array<Fr,4>@P){return subject(a);}run Run=Demo;
)")),
           context);
  });
  cases.run("filtered exact zero supports a subsequent fixed zero collect",
            [&] {
              verify(take(close(R"(
math fn subject(a:Fr)->Array<Fr,0>{let xs=filtered(range(4,1),fn(i)=>true,fn(i)=>a);return fixed(xs,fn(x)=>x);}
protocol Demo roles(P)(a:Fr@P)->(r:Array<Fr,0>@P){return subject(a);}run Run=Demo;
)")),
                     context);
            });
  cases.run("filtered positive upper count does not justify indexing", [] {
    refuses(check(R"(
math fn subject(a:Fr)->Fr{let xs=filtered(range(0,4),fn(i)=>true,fn(i)=>a);return at(xs,0);}
)"),
            "source.data-bound");
  });
  cases.run("filtered upper count does not justify fixed positive collect", [] {
    refuses(close(R"(
math fn subject(a:Fr)->Array<Fr,4>{let xs=filtered(range(0,4),fn(i)=>true,fn(i)=>a);return fixed(xs,fn(x)=>x);}
protocol Demo roles(P)(a:Fr@P)->(r:Array<Fr,4>@P){return subject(a);}run Run=Demo;
)"),
            "source.data-bound");
  });
  cases.run("source cardinality uses the enclosing work allowance", [] {
    auto project = take(check(R"(
math fn subject(a:Fr)->Array<Fr,0>{let xs=filtered(product(range(0,0),range(0,4)),fn(item)=>true,fn(item)=>a);return fixed(xs,fn(x)=>x);}
)"));
    std::vector<Declaration> declarations(project.declarations().begin(),
                                          project.declarations().end());
    auto subject = llvm::find_if(declarations, [](const auto &declaration) {
      return declaration.name == "subject";
    });
    require(subject != declarations.end(), "missing count subject");
    auto measure = [&](const Limits &limits) -> std::pair<bool, uint64_t> {
      source_detail::Work work{limits};
      source_detail::Semantics types(declarations, project.assets(), work);
      bool accepted = source_detail::checkFiniteContracts(
          types, declarations, *subject, *subject->body);
      if (!accepted)
        require(types.diagnostic && types.diagnostic->code == "source.limit",
                "count exhaustion became a mathematical condition");
      return {accepted, work.used};
    };
    auto [accepted, cost] = measure(Limits{});
    require(accepted && cost, "source count check failed");
    Limits limits;
    limits.work = cost;
    require(measure(limits).first, "exact count work boundary refused");
    limits.work = cost - 1;
    require(!measure(limits).first, "zero count hid exhausted extraction");
  });
  cases.run("factory parameters expand using actual caller operands", [&] {
    verify(take(close(R"(
domain fn relay(rows:domain<index>)->domain<index>{return rows;}
domain fn interval(lo:index,hi:index)->domain<index>{return relay(range(lo,hi));}
math fn subject(a:Fr)->Array<Fr,4>{return fixed(body=fn(i)=>a,rows=interval(index_id(0),index_id(4)));}
protocol Demo roles(P)(a:Fr@P)->(r:Array<Fr,4>@P){return subject(a);}run Run=Demo;
)")),
           context);
  });
  cases.run("empty count cannot hide unused factory zip admission", [] {
    refuses(close(R"(
domain fn selected(xs:Vector<Fr>,ys:Vector<Fr>,lo:index,hi:index)->domain<index>{let unused=zip(elements(xs),elements(ys));return range(lo,hi);}
math fn subject(xs:Vector<Fr>,ys:Vector<Fr>,a:Fr)->Array<Fr,0>{return fixed(selected(xs,ys,0,0),fn(i)=>a);}
protocol Demo roles(P)(xs:Vector<Fr>@P,ys:Vector<Fr>@P,a:Fr@P)->(r:Array<Fr,0>@P){return subject(xs,ys,a);}run Run=Demo;
)"),
            "source.data-bound");
  });
  cases.run("unused eager argument computation still requires its bound", [] {
    refuses(check(R"(
math fn ignore(a:Fr)->index{return 0;}
math fn subject(xs:Vector<Fr>)->Array<Fr,0>{return fixed(range(ignore(at(xs,0)),0),fn(i)=>1);}
)"),
            "source.data-bound");
  });
  cases.run("repeated same-shaped collections do not inherit other bounds", [] {
    refuses(check(R"(
math fn subject(xs:Vector<Fr>,ys:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){let a=mapped(xs,fn(x)=>x);let b=mapped(ys,fn(x)=>x);return at(b,i);}
)"),
            "source.data-bound");
  });
  cases.run("ordinary wrapper retains generic formation boundary", [] {
    refuses(close(R"(
math fn wrapper(rows:domain<index>,body:math fn(item:index)->Fr where item_from(item,rows))->Array<Fr,4>{return fixed(rows,body);}
math fn subject(a:Fr)->Array<Fr,4>{return wrapper(range(0,4),fn(i)=>a);}
protocol Demo roles(P)(a:Fr@P)->(r:Array<Fr,4>@P){return subject(a);}run Run=Demo;
)"),
            "source.data-bound");
  });
  for (StringRef mode : {"local", "math"})
    cases.run(
        "Local caller preserves " + mode + " finite helper formation", [&] {
          std::string definition =
              mode == "local"
                  ? "fn "
                    "local_fixed<I:Type+Copy+Drop,N:nat>(rows:domain<I>,body:"
                    "fn(item:I)->Fr effects(stop) where "
                    "item_from(item,rows))->Array<Fr,N> "
                    "effects(stop)=finite(\"local.collect.field_array\");\n"
                  : "";
          std::string callee = mode == "local" ? "local_fixed" : "fixed";
          refuses(close(definition +
                        "fn subject(a:Fr)->Array<Fr,4> effects(stop){return " +
                        callee +
                        "(range(0,4),fn(i)=>a);}\n"
                        "protocol Demo roles(P)(a:Fr@P)->(r:Array<Fr,4>@P) "
                        "effects(stop){return subject(a);}run Run=Demo;"),
                  "source.data-bound");
        });
  for (StringRef choice : {"domain", "callback", "predicate", "seed"})
    cases.run("witness rejects a different valid " + choice + " choice", [&] {
      auto source = choice == "predicate" ? R"(
math fn subject()->(Vector<Fr>,Vector<Fr>){let a=filtered(range(0,4),fn(i)=>true,fn(i)=>1);let b=filtered(range(0,4),fn(i)=>false,fn(i)=>1);return (a,b);}
protocol Demo roles(P)()->(r:(Vector<Fr>,Vector<Fr>)@P){return subject();}run Run=Demo;
)"
                    : choice == "seed"    ? R"(
math fn subject()->(Fr,Fr){let first:Fr=1;let second:Fr=2;let a=total(range(0,4),first,fn(s,i)=>s+1);let b=total(range(0,4),second,fn(s,i)=>s+1);return (a,b);}
protocol Demo roles(P)()->(r:(Fr,Fr)@P){return subject();}run Run=Demo;
)"
                                          : R"(
math fn subject()->(Vector<Fr>,Vector<Fr>){let lo:index=0;let next:index=1;let hi:index=4;let end:index=5;let a=mapped(range(lo,hi),fn(i)=>1);let b=mapped(range(next,end),fn(i)=>2);return (a,b);}
protocol Demo roles(P)()->(r:(Vector<Fr>,Vector<Fr>)@P){return subject();}run Run=Demo;
)";
      auto closed = take(close(source));
      verify(closed, context);
      bool changed = false;
      for (const auto &declaration : closed.declarations()) {
        if (declaration.name != "subject" || !declaration.body)
          continue;
        auto body = std::make_shared<Body>(*declaration.body);
        std::vector<FiniteComputation *> finite;
        for (auto &op : body->operations)
          if (auto *value = std::get_if<FiniteComputation>(&op.action))
            finite.push_back(value);
        require(finite.size() == 2, "expected two finite occurrences");
        if (choice == "callback")
          finite[0]->body = finite[1]->body;
        else if (choice == "predicate")
          finite[0]->predicate = finite[1]->predicate;
        else if (choice == "seed")
          finite[0]->operands = finite[1]->operands;
        else
          finite[0]->domainOperands = finite[1]->domainOperands;
        requireAdmitted(closed, declaration, *body);
        const_cast<Declaration &>(declaration).body = std::move(body);
        changed = true;
      }
      require(changed, "missing witness mutation subject");
      auto error = checkScopedSpecialization(closed);
      require(bool(error), "different valid occurrence choice was accepted");
      auto message = toString(std::move(error));
      require(message.find("source.scoped-specialization") != std::string::npos,
              "wrong finite occurrence witness refusal: " + message);
    });
  cases.run("witness requires occurrence form for a Math finite caller", [&] {
    auto closed = take(close(R"(
math fn wrapper(rows:domain<Fr>,body:math fn(item:Fr)->Fr where item_from(item,rows))->Vector<Fr>{return mapped(rows,body);}
fn both(rows:domain<Fr>,body:math fn(item:Fr)->Fr where item_from(item,rows))->(Vector<Fr>,Vector<Fr>){return (wrapper(rows,body),mapped(rows,body));}
protocol Demo roles(P)(xs:Vector<Fr>@P)->(r:(Vector<Fr>,Vector<Fr>)@P){return both(elements(xs),fn(x)=>x);}run Run=Demo;
)"));
    verify(closed, context);
    const Declaration *generic = nullptr;
    for (const auto &declaration : closed.declarations())
      if (declaration.name == "mapped" && declaration.body)
        generic = &declaration;
    require(generic && generic->inputs.size() == 1 &&
                generic->scopedArguments.size() == 1 &&
                generic->domainArguments.size() == 1,
            "missing Local caller's generic Math finite instance");
    bool changed = false;
    for (const auto &declaration : closed.declarations()) {
      if (declaration.name != "wrapper" || !declaration.body)
        continue;
      auto body = std::make_shared<Body>(*declaration.body);
      require(body->inputs == 1 && body->operations.size() == 1,
              "unexpected wrapper layout");
      auto &op = body->operations.front();
      const auto &finite = std::get<FiniteComputation>(op.action);
      require(finite.body.helper.index ==
                      generic->scopedArguments.front().index &&
                  finite.body.captures.empty() &&
                  finite.domain->identity ==
                      generic->domainArguments.front()->identity,
              "alternative instance must have the same callback and domain");
      // Reuse a real admitted instance with the same callback and domain, so
      // the alternative remains mathematically valid and well typed.
      op.action = HelperCall{
          generic->id, finite.domainOperands, generic->staticArguments, {}, {},
          {}};
      requireAdmitted(closed, declaration, *body);
      const_cast<Declaration &>(declaration).body = std::move(body);
      changed = true;
    }
    require(changed, "missing Math finite wrapper");
    auto error = checkScopedSpecialization(closed);
    require(bool(error), "generic form replaced canonical finite occurrence");
    auto message = toString(std::move(error));
    require(message.find("Math finite call requires occurrence expansion") !=
                std::string::npos,
            "alternative failed before the canonical-form check: " + message);
  });
  return cases.result();
}
